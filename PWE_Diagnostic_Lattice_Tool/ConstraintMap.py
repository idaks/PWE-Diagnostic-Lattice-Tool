from .LogicProgram import LogicProgram
from .LatticeNode import (
    Node,
    NodeEvalState,
    NumPWSType,
    NodeAmbiguityType,
)
from collections import defaultdict


class ConstraintMap:

    def __init__(self, constraints: list):
        self.constraints = constraints
        self.num_constraints = len(self.constraints)
        self.maximal_satisfiable_constraint_subsets = set([])
        self.minimal_unsatisfiable_constraint_subsets = set([])
        self.maximal_ambiguous_constraint_subsets = set([])
        self.minimal_unambiguous_constraint_subsets = set([])
        self.nodes = defaultdict(Node)

    def reset_explored_set(self):
        pass

    def update_num_pws(self, constraints, num_pws: int, num_pws_eval_type: NumPWSType):
        pass

    def check_node_num_pws(self, constraints):
        pass

    def check_ambiguity(self, constraints):
        pass

    def check_node_eval_state(self, constraints) -> NodeEvalState:
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

    def get_num_pws(self, seed, cnf_prog: LogicProgram):
        # TODO
        pass
