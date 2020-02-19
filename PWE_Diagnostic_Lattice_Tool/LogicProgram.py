from .LatticeNode import NodeAmbiguityType


class LogicProgram:

    def __init__(self):
        pass

    def check_sat(self, constraints) -> bool:
        pass

    def check_ambiguity(self, constraints) -> NodeAmbiguityType:
        """
        NodeAmbiguityType.unsat       == 0 --> UNSAT       (UNSAT)
        NodeAmbiguityType.ambiguous   == 1 --> UNAMBIGUOUS (SAT)
        NodeAmbiguityType.unambiguous == 2 --> AMBIGUOUS   (SAT)
        """
        pass

    def get_num_solutions(self, constraints) -> int:
        pass
