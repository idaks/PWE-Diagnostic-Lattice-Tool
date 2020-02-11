from .ConstraintMap import ConstraintMap
from .CNFProgram import CNFProgram
from .LatticeNode import (
    Node,
    NodeEvalState,
    NumPWSType,
    NodeAmbiguityType,
)
from collections import defaultdict


class BitConstraintMap(ConstraintMap):

    def __init__(self, constraints):
        ConstraintMap.__init__(self, constraints)
        self.constraints_set = set(constraints)
        self.constraint_to_int_map = dict(zip(constraints, range(self.num_constraints)))
        self.unexplored_set = set(range(2 ** self.num_constraints))
        self.explored_set = set([])
        self.nodes = defaultdict(Node)
