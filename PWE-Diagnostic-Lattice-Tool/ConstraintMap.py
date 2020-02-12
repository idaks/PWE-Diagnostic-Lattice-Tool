from .LogicProgram import LogicProgram
from collections import defaultdict
from .LatticeNode import (
    Node,
    NodeEvalState,
    NumPWSType,
)


class ConstraintMap:

    def __init__(self, constraints):
        self.constraints = constraints
        self.num_constraints = len(self.constraints)
        self.maximal_satisfiable_constraint_subsets = set([])
        self.minimal_unsatisfiable_constraint_subsets = set([])
        self.maximal_ambiguous_constraint_subsets = set([])
        self.minimal_unambiguous_constraint_subsets = set([])

    def update_num_pws(self, constraints, num_pws, num_pws_eval_type: NumPWSType):
        pass

    def check_node_num_pws(self, constraints):
        pass

    def check_ambiguity(self, constraints):
        pass

    def check_node_eval_state(self, constraints) -> NodeEvalState:
        pass

    def _check_node_sat_explicit_(self, constraints):
        pass

    def _check_node_sat_implicit_(self, constraints, mss_es=None, mus_es=None, mas_es=None, muas_es=None):
        """
        Use MSS-es, MUS-es, MAS-es and MUAS-es to determine if satisfiable
        :param constraints:
        :param mss_es:
        :param mus_es:
        :param mas_es:
        :param muas_es:
        :return: True/False, None if can't be determined
        """
        pass

    def check_sat(self, constraints):
        pass

    def get_unexplored(self):
        pass

    def get_unexplored_max(self):
        pass

    def block_down(self, constraints):
        pass

    def block_up(self, constraints):
        pass

    def grow(self, seed, cnf_prog: LogicProgram):
        pass

    def shrink(self, seed, cnf_prog: LogicProgram):
        pass

    def grow_ambiguous(self, seed, cnf_prog: LogicProgram):
        pass

    def shrink_unambiguous(self, seed, cnf_prog: LogicProgram):
        pass
