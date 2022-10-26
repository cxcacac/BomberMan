import random
import tornado.httpserver
import tornado.ioloop
import tornado.web
from collections import namedtuple
from datetime import datetime
import pandas as pd
import numpy as np
import json
import sys
import coloredlogs
import logging
from tornado.options import define, options

sys.path.append(r"event_driving")
logging.basicConfig(format='%(asctime)s,%(msecs)d %(levelname)-8s [%(filename)s:%(lineno)d] %(message)s',
    datefmt='%Y-%m-%d:%H:%M:%S',
    level=logging.DEBUG)
logger = logging.getLogger(__name__)
coloredlogs.install(level='DEBUG')
define("port", default=19105, help="run on the given port", type=int)

direction_tuple = namedtuple('MOVEDIRECTION', ['TOP', 'DOWN', 'LEFT', 'RIGHT', 'STOP', 'ERROR'])
release_tuple = namedtuple('RELEASEBOOM', ['TRUE', 'FALSE'])
MOVEDIRECTION = direction_tuple('TOP', 'DOWN', 'LEFT', 'RIGHT','STOP','ERROR')
RELEASEBOOM = release_tuple("true", "false")

HASH_INT = 1000000
MOVES = [[0,1],[0,-1],[-1,0],[1,0],[0,0]]  # 不是以坐标系作为判断，而是以行列坐标作为判断
ALL_DIRECTION_CHOICES = [0,1,2,3,4]
MOVES_DIRECTIONS_ARRAY = [MOVEDIRECTION.RIGHT, MOVEDIRECTION.LEFT, MOVEDIRECTION.TOP, MOVEDIRECTION.DOWN, MOVEDIRECTION.STOP, MOVEDIRECTION.ERROR]
RELEASE_BOOM_GAP = 9  # (可调)不能太少，因为可能不够撤离距离，影响吃分效率，同时可能会把自己堵死，必须要在7-9中间
PRINT_CURRENT_STATUS = False
BONUS_NPC_LEN_GAP = 10 # (可调)不能太小，如果对方智能体会躲避，而盲目地纠缠会错过了得分的时机；不能太大，因为可能到了分就被其它智能体吃了，路径规划是滞后的，大概在5-10左右
BONUS_BOOMABLE_LEN_GAP = 3 # (可调)就近处理刚炸完的箱子出来的元素，越大越容易先吃bonus，而不是先炸箱子
START_ATTACK_MAGICBOX_THRESHOLD = 1  # (不变)如果仅剩1个magic_box，那么就有都来吃这个分陷入僵局的可能，那么就可以开启堵门的攻击模式，防止进入僵局
RELEASE_BOOM_NPC_DISTANCE = 2  # (不变)在最后进攻的时候，相隔两个就可以放炸弹了，有堵门的可能，同时防止靠得太近，被1换1，这样也会安全一点，放炸弹也比较多
INFINITY_POSITIVE_VALUE = 100000000  # (不变)

class BaseElement:
    def __init__(self, row, col):
        self.loc = [row, col]
        self.loc_row = row
        self.loc_col = col
        self.loc_flat = row*HASH_INT + col


class Coordinate(BaseElement):
    def __init__(self, loc):
        super().__init__(loc[0], loc[1])


class NPC(BaseElement):
    def __init__(self, row, col, s, id):
        super().__init__(row,col)
        self.score = s
        self.npc_id = id
    

class Boom(BaseElement):
    def __init__(self, row, col):
        super().__init__(row,col)
        self.boom_danger_zones = []
        for i in range(5):
            self.boom_danger_zones.append((row + MOVES[i][0])*HASH_INT +
                                            col + MOVES[i][1])

class SelfBoom(Boom):
    def __init__(self, row, col):
        super().__init__(row,col)
        self.exist_time = 0

class Explode(BaseElement):
    def __init__(self, row, col, down, left, right, up):
        super().__init__(row, col)
        self.explode_danger_zones= []
        # 'activeExplodes': [{'col': 3, 'down': 0, 'left': 1, 'right': 1, 'row': 10, 'up': 1}]
        # 辐射范围的left, right, row, up不包括当前爆炸源的方块数
        self.explode_danger_zones.append(row*HASH_INT + col)
        for i in range(1,down+1):
            self.explode_danger_zones.append((row+i)*HASH_INT + col)
        for i in range(1,left+1):
            self.explode_danger_zones.append(row*HASH_INT+(col-i))
        for i in range(1,up+1):
            self.explode_danger_zones.append((row-i)*HASH_INT+col)
        for i in range(1,right+1):
            self.explode_danger_zones.append(row*HASH_INT+(col+i))            

class MagicBox(BaseElement):
    def __init__(self, row, col):
        super().__init__(row, col)

class BFSNode(BaseElement):
    def __init__(self, loc, pre, dir):
        super().__init__(loc[0], loc[1])
        self.prenode = pre
        self.to_direction = dir  # prenode到当前node走的方向
        
        
# Map提供的都是客观的价值信息，不做决策
class Map:
    def __init__(self):
        pass

    def parse(self,data):
        self.mapRows = int(data['gameMap']['mapRows'])
        self.mapCols = int(data['gameMap']['mapCols'])    
        self.maplist = data['gameMap']['mapList']
        self.npc_id = data['selfNpcId']
        self.game_id = None
        if data.__contains__('gameId'):
            self.game_id = data['gameId']
        
        # 下列变量不能重复使用，每次都优化
        self.control_npc = None
        self.other_npcs = {}
        self.other_npc_zones = []
        self.danger_zones = []
        self.control_npc_self_caused_danger_zones = []   # danger_zones包含control_npc_self_caused_danger_zones
        self.boom_zones = []  # 炸弹最中心的位置
        self.control_npc_release_boom_zones = []
        self.all_npc_scores = {}
        
        for npc_info in data['gameMap']['activeNpcs']:
            # 如果npc分数为负分，而且npc死了，会返回负分
            if npc_info['score'] < 0  or npc_info['col'] == -1 or npc_info['row'] == -1:
                continue
            tmp_npc = NPC(npc_info['row'], npc_info['col'], npc_info['score'], npc_info['npcId'])
            self.all_npc_scores[tmp_npc.npc_id] = tmp_npc.score
            
            if npc_info['npcId'] == self.npc_id:
                self.control_npc = tmp_npc
            else:
                self.other_npcs[tmp_npc.npc_id] = tmp_npc
                # 有其他npc的地方也是danger_zones，因为过去就相当于直接站在炸弹的中间不动
                self.danger_zones.append(tmp_npc.loc_flat)
                self.other_npc_zones.append(tmp_npc.loc_flat)
        # 按照分值进行排序
        self.sorted_all_npc_scores = sorted(self.all_npc_scores.items(), key=lambda x:x[1])
        
        self.all_booms = {}
        for boom_info in data['gameMap']['activeBooms']:
            boom_center_x = boom_info['row']
            boom_center_y = boom_info['col']
            tmp_boom = Boom(boom_center_x, boom_center_y)
            self.all_booms[tmp_boom.loc_flat] = tmp_boom
            self.danger_zones.extend(tmp_boom.boom_danger_zones)
            self.boom_zones.append(tmp_boom.loc_flat)
            
        # 炸弹爆炸后，炸弹会消失，火焰会存在
        self.all_explodes = {}
        for explode_info in data['gameMap']['activeExplodes']:
            tmp_explode = Explode(explode_info['row'], explode_info['col'], explode_info['down'], explode_info['left'], explode_info['right'], explode_info['up'])
            self.all_explodes[tmp_explode.loc_flat] = tmp_explode
            self.danger_zones.extend(tmp_explode.explode_danger_zones)
        
        self.all_magic_boxes = {}
        self.bonus_zones = []
        for magicbox_info in data['gameMap']['activeMagicBoxes']:
            tmp_magicbox = MagicBox(magicbox_info['row'], magicbox_info['col'])
            self.all_magic_boxes[tmp_magicbox.loc_flat] = tmp_magicbox
            self.bonus_zones.append(tmp_magicbox.loc_flat)
    
    def print_filtered_map(self):
        all_map = [['0']*self.mapCols for _ in range(self.mapRows)]
        for i in range(self.mapRows):
            for j in range(self.mapCols):
                for k in range(len(self.maplist[i][j])):
                    if self.maplist[i][j][k] and self.maplist[i][j][k] != ' ':
                        all_map[i][j] = self.maplist[i][j][k]
                        break
        print(np.array(all_map))
    
    def print_danger_zones(self):
        all_map = [[0]*self.mapCols for _ in range(self.mapRows)]
        for zone in self.danger_zones:
            x = zone//HASH_INT
            y = zone%HASH_INT
            if x < 0 or x >= self.mapRows:
                continue
            if y < 0 or y >= self.mapCols:
                continue
            all_map[x][y] -= 1
            if zone in self.control_npc_self_caused_danger_zones:
                all_map[x][y] -= 3
        print(np.array(all_map))
        
    def print_boom_zones(self):
        all_map = [[0]*self.mapCols for _ in range(self.mapRows)]
        for boom in self.all_booms.values():
            all_map[boom.loc_row][boom.loc_col] = -1
        print(np.array(all_map))

    def print_player_zones(self):
        all_map = [["0"]*self.mapCols for _ in range(self.mapRows)]
        for npc in self.other_npcs.values():
            all_map[npc.loc_row][npc.loc_col] = npc.npc_id
        all_map[self.control_npc.loc_row][self.control_npc.loc_col] = "me"
        print(np.array(all_map))

    def print_current_status(self):
        logging.warning("当前地图为:")
        self.print_filtered_map()
        logging.warning("炸弹位置为：")
        self.print_boom_zones()
        logging.warning("玩家位置为：")
        self.print_player_zones()
        logging.warning("危险区为：")
        self.print_danger_zones()
        logging.warning("当前价值表为：")
        print(np.array(self.runaway_values_table))

    def judge_controlnpc_is_highest_score(self):
        return (self.highest_score_npcid() == self.control_npc.npc_id)
    
    def judge_controlnpc_is_lowest_scrore(self):
        return (self.lowest_score_npcid()== self.control_npc.npc_id)
    
    def highest_score_npcid(self):
        return self.sorted_all_npc_scores[-1][0]
        
    def lowest_score_npcid(self):
        return self.sorted_all_npc_scores[0][0]
    
    # 找到分数最低的npc，如果自己的分数是最低的，那么就返回倒数第二低分的npc
    def lowest_score_npcid_except_me(self):
        for key_value_pair in self.sorted_all_npc_scores:
            if key_value_pair[0] == self.control_npc.npc_id:
                continue
            logging.info("当前分数最低的玩家id(除了当前npc):%s"%(key_value_pair[0]))
            return key_value_pair[0]
        
    # 先得到下一步计划的方向，然后再想着逃跑路径如何规划
    # 在这里初始化价值函数表
    def assign_reserve_step_choice(self, loc):
        logging.info("agent已经把下一步计划位置[%d, %d]传给了map"%(loc[0], loc[1]))
        self.runaway_values_table = [[0]*self.mapCols for _ in range(self.mapRows)] 
        for i in range(self.mapRows):
            for j in range(self.mapCols):
                self.runaway_values_table[i][j] = self.__runaway_value([i,j])
        
        # 给下一步的方向一个比较小的趋势分，尽量不影响大局，只是有相同价值选择的时候，尽量选择下一步规划好的方向
        self.runaway_values_table[loc[0]][loc[1]] += 10

    # 一个位置在逃跑的价值    
    def __runaway_value(self, loc):
        cur_value = 0
        # 如果是障碍物，那就最低分，没有逃跑的空间
        if self.judge_loc_has_unboomable_obstacles(loc):
            cur_value -= 300
        # 如果本地能不动，那就尽量不动
        if self.judge_loc_has_control_npc(loc):
            cur_value += 50
        # 如果只是不能去或者能去
        if self.judge_loc_accessible(loc):
            cur_value += 100
        else:
            cur_value -= 50
        # 如果处于自己创造的危险中，这个决策非常的重要，尤其被堵住的时候，有三秒的无敌时间。
        if self.judge_loc_in_selfmade_danger(loc): 
            cur_value -= 300
        # 如果在自己创造的炸弹的最中心
        if self.judge_loc_in_selfmade_boom_zones(loc):
            cur_value -= 50
        # 如果在其他人放的炸弹的最中心，需要尽快逃出来，不要高于有npc的方向，因为可能会连续被炸
        if self.judge_loc_in_boom_zones(loc):
            cur_value -= 10
        # 由于npc所在的位置本来就是danger_zone，有其他路可以走的时候不会走这个，但是不能走的时候，走npc那也没啥问题，权重不能太大
        if self.judge_loc_has_other_npc(loc):
            cur_value -= 20 
        # 如果有权益，而且能去
        if self.judge_loc_in_bonus(loc):
            cur_value += 100
            
        return cur_value 
    
    # 返回附近的npc的方向，包括当前控制npc所在的位置
    def near_npc_directions(self, loc):
        x = loc[0]
        y = loc[1]
        res = []
        for i in range(5):
            near_x = x + MOVES[i][0]
            near_y = y + MOVES[i][1]
            if self.judge_loc_has_other_npc([near_x, near_y]):
                res.append(i)
        return res
    
    # 返回四周的npc的方向，不包括当前控制npc所在的位置
    def adjacent_npc_directions(self, loc):
        x = loc[0]
        y = loc[1]
        res = []
        for i in range(4):
            adj_x = x + MOVES[i][0]
            adj_y = y + MOVES[i][1]
            if self.judge_loc_has_other_npc([adj_x, adj_y]):
                res.append(i)
        return res
    
    # 返回四周可以走的方向，不包括当前位置
    def adjacent_accessible_directions(self, loc):
        x = loc[0]
        y = loc[1]
        res = []
        for i in range(4):
            adj_x = x + MOVES[i][0]
            adj_y = y + MOVES[i][1]
            if self.judge_loc_accessible([adj_x, adj_y]):
                res.append(i)
        return res
    
    # 返回附近的可以移动的位置，包括当前位置，即停止不动
    def near_accessible_directions(self, loc):
        x = loc[0]
        y = loc[1]
        res = []
        for i in range(5):
            near_x = x + MOVES[i][0]
            near_y = y + MOVES[i][1]
            if self.judge_loc_accessible([near_x, near_y]):
                res.append(i)
        return res
    
    # 返回四周可以得分的方向
    def adjacent_bonus_directions(self, loc):
        x = loc[0]
        y = loc[1]
        res = []
        for i in range(4):
            adj_x = x + MOVES[i][0]
            adj_y = y + MOVES[i][1]
            if self.judge_loc_in_bonus([adj_x, adj_y]):
                res.append(i)
        return res
    
    # 返回附近可以得分的方向，包括当前位置
    def near_bonus_directions(self, loc):
        x = loc[0]
        y = loc[1]
        res = []
        for i in range(5):
            near_x = x + MOVES[i][0]
            near_y = y + MOVES[i][1]
            if self.judge_loc_in_bonus([near_x, near_y]):
                res.append(i)
        return res
    
    # 在给定选择下最高价值的移动方向
    # 注：choices应该是ALL_DIRECTION_CHOICES的一个值
    def best_run_away_direction(self, loc, available_choices):
        # choices = [1,2,3,4,5]
        # values = {1:5,2:7,3:6,4:8,5:1}
        # print(max(choices, key=lambda x:values[x])) # 4
        if len(available_choices) == 0:
            logging.warning("暂时没有可用的移动选项, 只能挑一个价值高和扣分少的! (也包括停止不动)")
            res_idx = max(ALL_DIRECTION_CHOICES, key=lambda x: self.runaway_values_table[MOVES[x][0]+loc[0]][MOVES[x][1]+loc[1]])
            self.print_current_status()
            return res_idx 
        else:
            # 返回拥有最大价值的位置
            res_idx = max(available_choices, key=lambda x: self.runaway_values_table[MOVES[x][0]+loc[0]][MOVES[x][1]+loc[1]])
            return res_idx

    # 满足accessible的都是可以runaway的方向
    def next_best_runaway_direction(self, loc):
        safe_choices = self.near_accessible_directions(loc)
        return self.best_run_away_direction(loc, safe_choices)

    # 判断一个位置是否处于危险区中
    def judge_loc_in_danger(self, loc):
        hash_loc = HASH_INT*loc[0] + loc[1]
        return (hash_loc in self.danger_zones)
    
    # 判断一个位置是否处在自己创造的危险区（即自己的炸弹区中）
    def judge_loc_in_selfmade_danger(self, loc):
        hash_loc = HASH_INT*loc[0] + loc[1]
        return (hash_loc in self.control_npc_self_caused_danger_zones)
    
    # 判断一个位置包含礼物，同时不能在危险区内
    def judge_loc_in_bonus(self, loc):
        hash_loc = HASH_INT*loc[0] + loc[1]
        if hash_loc in self.danger_zones:
            return False
        return (hash_loc in self.bonus_zones)
    
    # 判断一个位置是否有npc
    def judge_loc_has_other_npc(self, loc):
        hash_loc = HASH_INT*loc[0] + loc[1]
        return (hash_loc in self.other_npc_zones)
    
    # 判断是否有可炸开的箱子
    def judge_loc_has_boomable_box(self, loc):
        return self.maplist[loc[0]][loc[1]][0] == '2'
    
    # 判断一个位置是否在自己的炸弹中心
    def judge_loc_in_selfmade_boom_zones(self, loc):
        hash_loc = HASH_INT*loc[0] + loc[1]
        return (hash_loc in self.control_npc_release_boom_zones)
    
    # 判断一个位置是否在炸弹中心
    def judge_loc_in_boom_zones(self, loc):
        hash_loc = HASH_INT*loc[0] + loc[1]
        return (hash_loc in self.boom_zones)
    
    # 评估一个位置是否有不能炸掉的障碍物，边界也算在内
    def judge_loc_has_unboomable_obstacles(self, loc):
        if loc[0] < 0 or loc[0] >= self.mapRows:
            return True
        if loc[1] < 0 or loc[1] >= self.mapCols:
            return True
        return self.maplist[loc[0]][loc[1]][0] == '0'

    # 评估一个位置能不能在下一步走到，根据边界、危险区、障碍进行判断
    def judge_loc_accessible(self, loc):
        x = loc[0]
        y = loc[1]
        # 如果边界外
        if x < 0 or x >= self.mapRows:
            return False
        if y < 0 or y >= self.mapCols:
            return False
        # 如果处于危险区
        if self.judge_loc_in_danger(loc):
            return False
        # 如果有障碍，包括可炸毁障碍物和不可炸毁障碍物
        if self.maplist[x][y][0] == '0' or self.maplist[x][y][0] == '2':
            return False
        return True
    
    # 判断当前位置有npc，主要减少得分时候消耗的多余的路径
    def judge_loc_has_control_npc(self, loc):
        return HASH_INT*loc[0] + loc[1] == self.control_npc.loc_flat
    
    # 评估附近是否有npc
    def judge_loc_has_npc_around(self, loc):
        return (len(self.near_npc_directions(loc)) > 0)
        
    # 评估附近是否有可以炸开的箱子，主要用于放炸弹
    def judge_adjacent_has_boomable_box(self, loc):
        for i in range(4):
            adj_x = loc[0] + MOVES[i][0]
            adj_y = loc[1] + MOVES[i][1]
            if self.judge_loc_has_boomable_box([adj_x, adj_y]):
                return True
        return False
    
    # 评估附近有权益
    def judge_adjacent_has_bonus_magicbox(self, loc):
        return (len(self.adjacent_bonus_directions(loc)) > 0)
    
    # 判断一个决策是否撞墙
    def judge_controlnpc_bump_into_obstacles(self, choice):
        next_x = self.control_npc.loc_row + MOVES[choice][0]
        next_y = self.control_npc.loc_col + MOVES[choice][1]
        if next_x < 0 or next_x >= self.mapRows:
            return True
        if next_y < 0 or next_y >= self.mapCols:
            return True
        return (self.maplist[next_x][next_y] == '0' or self.maplist[next_x][next_y] == '2')
    
    # 放炸弹后能够躲避的方向，必须要能够走看到两步，否则就有炸到自己的可能
    def run_away_directions_after_release_boom(self, loc):
        # 注意不能stop
        x = loc[0]
        y = loc[1]
        res = []
        for i in range(4):
            next_x = x + MOVES[i][0]
            next_y = y + MOVES[i][1]
            if not self.judge_loc_accessible([next_x, next_y]):
                continue
            for j in range(4):
                nnext_x = next_x + MOVES[j][0]
                nnext_y = next_y + MOVES[j][1]
                # 如果回到了第一个位置
                if nnext_x == x and nnext_y == y:
                    continue
                # 如果最后的出口位置有npc在附近，那么也不要放，因为可能会把自己堵死，比如 最后在npc那要出来被溜了一路炸弹
                if self.judge_loc_has_npc_around([nnext_x, nnext_y]):
                    continue
                if self.judge_loc_accessible([nnext_x, nnext_y]):
                    res.append(i)
                    break
        return res
    
    # 返回到指定位置的npc路径
    def bfs_find_target_npc_path(self, src, dst):
        start_node = BFSNode(src, None, None)
        queue = []
        visited = []
        queue.append(start_node)
        visited.append(start_node.loc_flat)
        while len(queue)>0:
            for i in range(len(queue)):
                cur_node = queue.pop(0)
                for j in range(4):
                    next_x = cur_node.loc_row+MOVES[j][0]
                    next_y = cur_node.loc_col+MOVES[j][1]
                    # 如果已经到边界上，或者遇到障碍物
                    if next_x < 0 or next_x >= self.mapRows:
                        continue
                    if next_y < 0 or next_y >= self.mapCols:
                        continue
                    if self.maplist[next_x][next_y][0] == '0':
                        continue
                    next_node = BFSNode([next_x, next_y], cur_node, j)
                    # 如果已经遍历过
                    if next_node.loc_flat in visited:
                        continue
                    if next_x == dst[0] and next_y == dst[1]:
                        all_path = ""
                        tmp_node = next_node
                        heading_direction = None
                        while tmp_node.prenode != None:
                            heading_direction = tmp_node.to_direction
                            all_path = MOVES_DIRECTIONS_ARRAY[heading_direction][0] + all_path
                            tmp_node = tmp_node.prenode
                        return heading_direction, len(all_path)
                    queue.append(next_node)
                    visited.append(next_node.loc_flat)
        return -1,-1

   # 返回固定距离范围内是否有NPC
    def bfs_judge_fixed_distance_has_npc_around(self, src, distance):
        if self.judge_loc_has_other_npc(src):
            return True
        start_node = BFSNode(src, None, None)
        queue = []
        visited = []
        queue.append(start_node)
        visited.append(start_node.loc_flat)
        cnt = 0
        while cnt < distance:
            cnt += 1
            for i in range(len(queue)):
                cur_node = queue.pop(0)
                for j in range(4):
                    next_x = cur_node.loc_row+MOVES[j][0]
                    next_y = cur_node.loc_col+MOVES[j][1]
                    # 如果已经到边界上，或者遇到障碍物
                    if next_x < 0 or next_x >= self.mapRows:
                        continue
                    if next_y < 0 or next_y >= self.mapCols:
                        continue
                    if self.maplist[next_x][next_y][0] == '0':
                        continue
                    next_node = BFSNode([next_x, next_y], cur_node, j)
                    if next_node.loc_flat in visited:
                        continue
                    if self.judge_loc_has_other_npc([next_x, next_y]):
                        logging.info("在[%d,%d]位置找到了距离%d步内的NPC"%(next_x, next_y, cnt))
                        return True
                    queue.append(next_node)
                    visited.append(next_node.loc_flat)
        return False
    
    # BFS返回距loc最近距离的积分位置点，最短路径的方向，路径长度
    # 如果没有的话，则返回[-1,inifinity]
    def bfs_find_nearest_bonus_path(self, loc):
        start_node = BFSNode(loc, None, None)
        queue = []
        visited = []
        queue.append(start_node)
        visited.append(start_node.loc_flat)
        while len(queue) > 0:
            for i in range(len(queue)):
                cur_node = queue.pop(0)
                for j in range(4):
                    next_x = cur_node.loc_row + MOVES[j][0]
                    next_y = cur_node.loc_col + MOVES[j][1]
                    # 如果已经到边界上，或者遇到障碍物
                    if next_x < 0 or next_x >= self.mapRows:
                        continue
                    if next_y < 0 or next_y >= self.mapCols:
                        continue
                    if self.maplist[next_x][next_y][0] == '0':
                        continue   
                    # 最短路径上不能包含其它npc，否则这个路径规划基本没什么用，去了也是被先吃掉
                    if self.judge_loc_has_other_npc([next_x, next_y]):
                        continue
                    next_node = BFSNode([next_x, next_y], cur_node, j)
                    if next_node.loc_flat in visited:
                        continue
                    # 如果这个位置是magic_box
                    if self.judge_loc_in_bonus([next_x, next_y]):
                        all_path = ""
                        tmp_node = next_node
                        heading_direction = None
                        while tmp_node.prenode != None:
                            heading_direction = tmp_node.to_direction
                            all_path = MOVES_DIRECTIONS_ARRAY[heading_direction][0] + all_path
                            tmp_node = tmp_node.prenode
                        return heading_direction, len(all_path)
                    queue.append(next_node)
                    visited.append(next_node.loc_flat)
        return -1,INFINITY_POSITIVE_VALUE 

    def bfs_find_nearest_boomable_box_path(self, loc):
        start_node = BFSNode(loc, None, None)
        queue = []
        visited = []
        queue.append(start_node)
        visited.append(start_node.loc_flat)
        while len(queue) > 0:
            for i in range(len(queue)):
                cur_node = queue.pop(0)
                for j in range(4):
                    next_x = cur_node.loc_row + MOVES[j][0]
                    next_y = cur_node.loc_col + MOVES[j][1]
                    # 如果已经到边界上，或者遇到障碍物
                    if next_x < 0 or next_x >= self.mapRows:
                        continue
                    if next_y < 0 or next_y >= self.mapCols:
                        continue
                    if self.maplist[next_x][next_y][0] == '0':
                        continue   
                    next_node = BFSNode([next_x, next_y], cur_node, j)
                    if next_node.loc_flat in visited:
                        continue
                    # 如果这个位置是积分点，包括可以炸的箱子和可以吃的积分
                    if self.judge_loc_has_boomable_box([next_x, next_y]):
                        all_path = ""
                        tmp_node = next_node
                        heading_direction = None
                        while tmp_node.prenode != None:
                            heading_direction = tmp_node.to_direction
                            all_path = MOVES_DIRECTIONS_ARRAY[heading_direction][0] + all_path
                            tmp_node = tmp_node.prenode
                        return heading_direction, len(all_path)
                    queue.append(next_node)
                    visited.append(next_node.loc_flat)
        return -1, INFINITY_POSITIVE_VALUE          
                      
# 攻击：
# (1) 按照BFS来寻找最短路径，因为不计算可炸障碍物作为路障，因此路途上遇到箱子就要炸掉
# (2) 如果bonus更近，那么就要先吃bonus
# (3) 如果到了npc附近，那么就要逃跑

# 逃跑，往最安全的地方跑
# (1) 如果npc在附近，就有放炸弹的可能
# (2) 如果道具在附近，就有放炸弹的可能
# (3) 放不放炸弹，就要看这个炸弹会不会把自己的路堵死，如果不会，那么就会放炸弹。

class Agent:
    def __init__(self):
        self.m_map = Map()
        self.not_release_boom_cnt = 0
        self.control_npc_release_booms = []
        self.save_game_id = None
    
    def reset(self):
        self.not_release_boom_cnt = 0
        self.control_npc_release_booms = []

    def step(self, data):
        self.m_map.parse(data)
        
        # 重置缓存逻辑
        if self.save_game_id == None or self.m_map.game_id != self.save_game_id:
            logging.info("新游戏,重置程序缓存")
            self.reset()
            self.save_game_id = self.m_map.game_id
        
        # 必须先渲染自己造成的危险区，才能决策
        for boom in self.control_npc_release_booms:
            self.m_map.control_npc_self_caused_danger_zones.extend(boom.boom_danger_zones)
            self.m_map.control_npc_release_boom_zones.append(boom.loc_flat)
        
        move_choice, release_boom_choice = self.score_attack_run_decision()

        # 没有放炸弹，要统计步数
        if release_boom_choice == RELEASEBOOM.FALSE:
            self.not_release_boom_cnt += 1
            if self.not_release_boom_cnt == RELEASE_BOOM_GAP:
                logging.warning("%d步没有放炸弹了,必须要尝试放一个炸弹"%(self.not_release_boom_cnt))
                move_choice, release_boom_choice = self.try_release_boom_and_run_away()  
                if release_boom_choice == RELEASEBOOM.FALSE:
                    logging.error("当前位置放炸弹会有问题! 就算扣分也不要去放炸弹!")              
    
        if release_boom_choice == RELEASEBOOM.TRUE:
            self.not_release_boom_cnt = 0
            new_boom = SelfBoom(self.m_map.control_npc.loc[0], self.m_map.control_npc.loc[1])
            self.control_npc_release_booms.append(new_boom)

        # 无论放不放炸弹，炸弹的存在时间都+1
        # 可能会有迭代器失效的问题    
        clear_idx = []  
        for i in range(len(self.control_npc_release_booms)):
            self.control_npc_release_booms[i].exist_time += 1
            if self.control_npc_release_booms[i].exist_time > 3:
                clear_idx.append(i)
            
        for idx in clear_idx:
            logging.info("炸弹已失效,位置:[%d,%d]，请检查!"%(self.control_npc_release_booms[idx].loc_row,
                                            self.control_npc_release_booms[idx].loc_col))
            self.control_npc_release_booms.pop(idx)
            
        logging.info("此时控制npc在场上共有%d个自己放的炸弹以及对应的爆炸区域"%(len(self.control_npc_release_booms)))
        
        logging.info("控制npc当前信息:位置[%d,%d],分数:[%d]"%(self.m_map.control_npc.loc_row, 
                                                            self.m_map.control_npc.loc_col, 
                                                            self.m_map.control_npc.score))
        if PRINT_CURRENT_STATUS:
            self.m_map.print_current_status()
        return move_choice, release_boom_choice
    
    # 得分-攻击-逃跑策略
    def score_attack_run_decision(self):
        control_npc_place = self.m_map.control_npc.loc
        step_choice = self.path_planing_for_next_step_choice(control_npc_place)
        
        # 将当前选择给map赋值，在这个函数下初始化函数
        self.m_map.assign_reserve_step_choice([control_npc_place[0] + MOVES[step_choice][0], 
                                               control_npc_place[1] + MOVES[step_choice][1]])
        
        # 先看当前位置是否有危险，再看规划的方向去不去
        if self.m_map.judge_loc_has_npc_around(control_npc_place):
            logging.info("附近有npc,调整路线,并准备放炸弹...")
            return self.try_release_boom_and_run_away()
        
        # 如果先判断危险区，在跑路，那么可能一直都不放炸弹，然后被扣分，被换
        if self.m_map.judge_loc_in_danger(control_npc_place):
            logging.info("在危险区中,往安全处走...")
            return self.just_run_away()
                
        # 在路途中，如果附近有权益，那么可以先吃权益
        if self.m_map.judge_adjacent_has_bonus_magicbox(control_npc_place):
            avaiable_bonus_choices = self.m_map.adjacent_bonus_directions(control_npc_place)
            eat_bonus_move_choice = self.m_map.best_run_away_direction(control_npc_place,avaiable_bonus_choices)
            logging.info("四周有盒子奖励, 先吃盒子...")
            return MOVES_DIRECTIONS_ARRAY[eat_bonus_move_choice], RELEASEBOOM.FALSE   
                
        if self.m_map.judge_adjacent_has_boomable_box(control_npc_place):
            logging.info("前进路上有可炸障碍物,调整路线,并准备放炸弹...")
            return self.try_release_boom_and_run_away()
        
        # 如果现在地图上，magicbox很少，可能会有都吃一个分进入僵局，那么设置START_ATTACK_MAGICBOX_THRESHOLD，
        # 以转为进攻模式，需要由RELEASE_BOOM_NPC_DISTANCE决定开始放炸弹的距离
        if len(self.m_map.all_magic_boxes) <= START_ATTACK_MAGICBOX_THRESHOLD:
            if self.m_map.bfs_judge_fixed_distance_has_npc_around(control_npc_place, RELEASE_BOOM_NPC_DISTANCE):           
                logging.info("附近%d步内有npc,调整路线,并准备放炸弹..."%(RELEASE_BOOM_NPC_DISTANCE))
                return self.try_release_boom_and_run_away()

        # 如果最短路径的方向会踏入危险区，那么就换成逃跑策略
        if self.m_map.judge_loc_in_danger([control_npc_place[0] + MOVES[step_choice][0], 
                                           control_npc_place[1]+ MOVES[step_choice][1]]):
            logging.info("路径规划的方向不可进入,调整策略,往安全处走...")
            return self.just_run_away()
    
        return MOVES_DIRECTIONS_ARRAY[step_choice], RELEASEBOOM.FALSE
    
    # 做一些路径规划
    def path_planing_for_next_step_choice(self, loc):
        # 找分数最低的npc攻击
        target_npc_id = self.m_map.lowest_score_npcid_except_me()
        victim_place = self.m_map.other_npcs[target_npc_id].loc
        heading_npc_direction, heading_npc_len = self.m_map.bfs_find_target_npc_path(loc, victim_place)
        # 找有bonus的地方出发
        heading_bonus_direction, heading_bonus_len = self.m_map.bfs_find_nearest_bonus_path(loc)
        # 找有boomable_box的地方出发
        heading_boomable_direction, heading_boomable_len = self.m_map.bfs_find_nearest_boomable_box_path(loc)

        # 如果当前不是最高分，还是以抢分为主
        if not self.m_map.judge_controlnpc_is_highest_score():
            logging.info("当前npc不是最高分, 尽量先不要去追npc, 先要先得分")
            # 加1000是为了最后没有bonus和boomable的时候，必须要追
            heading_npc_len = INFINITY_POSITIVE_VALUE - 1000
        
        len_dict = {"bonus": heading_bonus_len, "npc":heading_npc_len+BONUS_NPC_LEN_GAP, "boomable":heading_boomable_len+BONUS_BOOMABLE_LEN_GAP}
        # 超最短路径的方向
        heading_choice = min(len_dict, key=len_dict.get)
        
        heading_direction = None
        if heading_choice == "bonus":
            heading_direction = heading_bonus_direction
            logging.info("路径规划结果:下一步会向吃积分方向出发！")
        elif heading_choice == "boomable":
            heading_direction = heading_boomable_direction
            logging.info("路径规划结果:下一步会向爆炸箱子方向出发！")
        else:
            heading_direction = heading_npc_direction
            logging.info("路径规划结果:下一步会进攻npc!")
            
        if self.m_map.judge_loc_has_unboomable_obstacles([loc[0] + MOVES[heading_direction][0], 
                                                          loc[1] + MOVES[heading_direction][1]]):
            logging.error("寻路算法有问题,下一步是不可移动障碍物!")
        
        return heading_direction

    # 只逃跑，炸弹也不放，活下来是第一位
    def just_run_away(self):
        run_away_choice = self.m_map.next_best_runaway_direction(self.m_map.control_npc.loc)
        return MOVES_DIRECTIONS_ARRAY[run_away_choice], RELEASEBOOM.FALSE
        
    # 逃跑，就是如果下一步能跑路，那么直接放炸弹
    # 从可选路径中选择一个价值最高的路径，并且要放炸弹
    def try_release_boom_and_run_away(self):
        run_away_choice = self.on_release_boom()
        # 返回ERROR则不要放炸弹
        if MOVES_DIRECTIONS_ARRAY[run_away_choice] == MOVEDIRECTION.ERROR:
            if self.m_map.judge_loc_accessible(self.m_map.control_npc.loc):
                logging.info("如果不放炸弹,此处是安全的,可以先暂停不动")
                return MOVEDIRECTION.STOP, RELEASEBOOM.FALSE
            else:
                run_away_choice = self.m_map.next_best_runaway_direction(self.m_map.control_npc.loc)
            release_boom_choice = RELEASEBOOM.FALSE
        else:
            release_boom_choice = RELEASEBOOM.TRUE
        
        return MOVES_DIRECTIONS_ARRAY[run_away_choice], release_boom_choice
            
    # 查看放炸弹之后还有没有选择
    def on_release_boom(self):
        available_choices = self.m_map.run_away_directions_after_release_boom(self.m_map.control_npc.loc)
        # 如果放炸弹必定会被炸到，没有余地，就返回MOVEDIRECTION.ERROR
        if len(available_choices)== 0:
            return -1
        else:
            best_runaway_choice = self.m_map.best_run_away_direction(self.m_map.control_npc.loc, available_choices)
            return best_runaway_choice
    
    # 测试用
    def test_step(self, data):
        direction = random.choice(list(MOVEDIRECTION))
        release_boom = random.choice(list(RELEASEBOOM))
        return direction, release_boom
    

runner = Agent()

class ActionHandler(tornado.web.RequestHandler):
    def post(self):
        data = json.loads(self.request.body)
        receive_time = datetime.now()
        print("调用前时间:",receive_time.strftime('%Y-%m-%d %H:%M:%S.%f'))
        move, release = runner.step(data)
        d = {"moveType": move, "releaseBoom": release}
        print('最终决策:', d)
        self.write(d)
        write_time = datetime.now()
        print("调用后时间:",write_time.strftime('%Y-%m-%d %H:%M:%S.%f'))
        timedelta = write_time - receive_time
        print("总耗时(ms):", timedelta.microseconds/1000)

    def get(self):
        self.write("http test")


if __name__ == '__main__':
    app = tornado.web.Application(
        handlers=[(r'/player/action', ActionHandler)]
    )
    http_server = tornado.httpserver.HTTPServer(app)
    print(options.port)
    http_server.listen(options.port)
    tornado.ioloop.IOLoop.instance().start()