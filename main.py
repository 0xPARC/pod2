#!/usr/bin/env python3

from math import log

MAX_ST = 20
MAX_SIG = 2
MAX_POD = 1

mt_proof_32 = 142
op_verify_gadget_mt_fixed = mt_proof_32 * 5
op_verify_gadget_base_cur_rand_access = 230
op_verify_gadget_base_better_rand_access = 56
op_verify_gadget_base_cur_logic = 20
# op_verify_gadget_base = op_verify_gadget_base_cur_logic + \
#         op_verify_gadget_base_cur_rand_access
op_verify_gadget_base = op_verify_gadget_base_cur_logic + \
        op_verify_gadget_base_better_rand_access
op_verify_gadget_hash = 5
op_verify_gadget_non_inclusion = 5 + 12
op_verify_gadget_custom_pred = 100
op_verify_gadget_base = op_verify_gadget_base + \
        op_verify_gadget_hash + \
        op_verify_gadget_non_inclusion + \
        op_verify_gadget_custom_pred
value_of_unique = 5
op_verify_total = op_verify_gadget_mt_fixed + \
        op_verify_gadget_base + \
        sum([op_verify_gadget_base + value_of_unique * i for i in range(MAX_ST)])
signed_pod_verify_gadget = 5064
main_pod_verify_gadget = 5064
main_pod_circuit = op_verify_total + \
        MAX_SIG * signed_pod_verify_gadget + \
        MAX_POD * main_pod_verify_gadget
zk_cost = 11000

print(f'avg(op_verify_gadget) = {op_verify_total//MAX_ST}')
print(f'main_pod_circuit = {main_pod_circuit}')
print(f'zk_main_pod_circuit = {main_pod_circuit + zk_cost}')
print(f'zk_main_pod_circuit = 2^{log(main_pod_circuit + zk_cost, 2)}')
