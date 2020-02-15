from .LogicProgram import LogicProgram
from PW_explorer.run_clingo import run_clingo
from PW_explorer.run_dlv import run_dlv
from PW_explorer.load_worlds import load_worlds
from .LatticeNode import NodeAmbiguityType


class ASP_LogicProgram(LogicProgram):

    def __init__(self, initial_encoding: str, constraint_keyword: str='comp', reasoner: str='clingo'):
        """
        :param initial_encoding: Encoding w/o any of the constraints turned on.
        :param constraint_keyword: The arity 1 relation name to use to turn constraints on.
        :param reasoner: Reasoner to use. Choices: 'clingo' (default) or 'dlv'.
        """
        LogicProgram.__init__(self)
        self.encoding = initial_encoding
        self.constraint_keyword = constraint_keyword
        self.reasoner = reasoner

    def run_reasoner(self, constraints: list, num_pws: int):

        run_reasoner_func = {'clingo': run_clingo,
                             'dlv': run_dlv,
                            }[self.reasoner]
        constraint_activations = "\n".join(["{}({}).".format(self.constraint_keyword, c) for c in set(constraints)])
        map_soln, md = run_reasoner_func(self.encoding + '\n' + constraint_activations, num_solutions=num_pws)
        pw_rel_dfs, rel_schemas, pws = load_worlds(map_soln, silent=True)
        return pw_rel_dfs, rel_schemas, pws

    def get_num_solutions(self, constraints: list):
        _, _, pws = self.run_reasoner(constraints=constraints, num_pws=0)
        return len(pws)

    def check_sat(self, constraints):

        _, _, pws = self.run_reasoner(constraints, num_pws=1)

        return len(pws) >= 1

    def check_ambiguity(self, constraints) -> NodeAmbiguityType:
        """
        NodeAmbiguityType.unsat       == 0 --> UNSAT       (UNSAT)
        NodeAmbiguityType.unambiguous == 1 --> UNAMBIGUOUS (SAT)
        NodeAmbiguityType.ambiguous   == 2 --> AMBIGUOUS   (SAT)
        """
        _, _, pws = self.run_reasoner(constraints, num_pws=2)

        if len(pws) >= 2:
            return NodeAmbiguityType.ambiguous
        elif len(pws) == 1:
            return NodeAmbiguityType.unambiguous
        else:
            return NodeAmbiguityType.unsat
