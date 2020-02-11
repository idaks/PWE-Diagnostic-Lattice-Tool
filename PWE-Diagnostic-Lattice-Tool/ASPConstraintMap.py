from .ConstraintMap import ConstraintMap
from .CNFProgram import CNFProgram
from PW_explorer.run_clingo import run_clingo
from PW_explorer.load_worlds import load_worlds
from .LatticeNode import (
    Node,
    NodeEvalState,
    NumPWSType,
    NodeAmbiguityType,
)
from collections import defaultdict


class ASPConstraintMap(ConstraintMap):

    COMP_COUNT_RULE = "on_comp(N) :- #count {P : comp(P)} = N."
    COMP_MAXIMIZE_RULE = "#maximize {N : on_comp(N)}."

    def __init__(self, constraints):
        ConstraintMap.__init__(self, constraints)
        self.constraints_set = set(constraints)
        self.encoding = "\n".join(["comp({0}) ; not comp({0}).".format(c) for c in self.constraints])
        self.nodes = defaultdict(Node)

    def get_unexplored(self):
        map_soln, _ = run_clingo(self.encoding, num_solutions=1)
        pw_rel_dfs, rel_schemas, pws = load_worlds(map_soln, silent=True)
        if len(pws) == 0:
            return None
        if 'comp_1' not in pw_rel_dfs:
            return {}
        comp_1_dfs = pw_rel_dfs['comp_1']
        comp_1_dfs = comp_1_dfs[comp_1_dfs['pw'] == 1]
        comps = set(list(comp_1_dfs['x1']))
        return comps

    def get_unexplored_max(self):
        map_soln, _ = run_clingo(self.encoding + '\n' + self.COMP_COUNT_RULE + '\n' + self.COMP_MAXIMIZE_RULE,
                                 num_solutions=0)
        pw_rel_dfs, rel_schemas, pws = load_worlds(map_soln, silent=True)
        if len(pws) == 0:
            return None
        if 'comp_1' not in pw_rel_dfs:
            return {}
        max_pw = max(pws, key=lambda pw: -pw.pw_soln)
        max_pw_id = max_pw.pw_id
        comp_1_dfs = pw_rel_dfs['comp_1']
        comp_1_dfs = comp_1_dfs[comp_1_dfs['pw'] == max_pw_id]
        comps = set(list(comp_1_dfs['x1']))
        return comps

    def block_down(self, n):
        self.encoding += '\n' + " ; ".join(["comp({})".format(c) for c in (self.constraints_set - set(n))]) + "."

    def block_up(self, n):
        self.encoding += '\n' + " ; ".join(["not comp({})".format(c) for c in set(n)]) + "."

    def grow(self, seed, cnf_prog: CNFProgram, update_map_with_mss=True, update_map_with_intermediate_results=True):
        seed = set(seed)
        iter_set = self.constraints_set - seed
        for c in list(iter_set):
            if cnf_prog.check_sat(seed.union({c})):
                seed.add(c)

        if update_map_with_mss:
            self.maximal_satisfiable_constraint_subsets.add(frozenset(seed))

        return seed

    def shrink(self, seed, cnf_prog: CNFProgram, update_map_with_mus=True, update_map_with_intermediate_results=True):
        seed = set(seed)
        iter_set = seed.copy()
        for c in iter_set:
            if not cnf_prog.check_sat(seed.difference({c})):
                seed.remove(c)

        if update_map_with_mus:
            self.minimal_unsatisfiable_constraint_subsets.add(frozenset(seed))

        return seed

    def _check_node_sat_(self, constraints):
        """
        explicit check in the self.nodes dict
        :param constraints:
        :return:
        """
        n = frozenset(constraints)
        if n in self.nodes:
            return self.nodes[n].is_sat()
        return None

    def check_sat(self, n, mss_es: set=None, mus_es: set=None, mas_es: set=None, muas_es: set=None):
        """
        :param n:
        :param mss_es: Set of frozensets (each frozenset corresponds to an MSS)
        :param mus_es: Set of frozensets (each frozenset corresponds to an MUS)
        :param mas_es: Set of frozensets (each frozenset corresponds to an MAS)
        :param muas_es: Set of frozensets (each frozenset corresponds to an MUAS)
        :return:
        """

        k = self._check_node_sat_(n)
        if k is not None:
            return k

        if mss_es is None:
            mss_es = self.maximal_satisfiable_constraint_subsets
        if mus_es is None:
            mus_es = self.minimal_unsatisfiable_constraint_subsets
        if mas_es is None:
            mas_es = self.maximal_ambiguous_constraint_subsets
        if muas_es is None:
            muas_es = self.minimal_unambiguous_constraint_subsets

        n = set(n)

        for c in mus_es.union(mss_es):
            if n <= c:
                # SAT if ancestor of an MUS or an MSS
                return True
            elif n >= c:
                # UNSAT if descendant of an MUS or an MSS
                return False

        for c in muas_es.union(mas_es):
            if n <= c:
                # SAT if ancestor of MUAS or MAS
                return True

        return None

    def update_num_pws(self, constraints, num_pws, num_pws_eval_type: NumPWSType):
        self.nodes[frozenset(constraints)].update_num_pws(num_pws=num_pws, num_pws_eval_type=num_pws_eval_type)

    def check_node_num_pws(self, constraints):

        # Explicit Check
        n = frozenset(constraints)
        if n in self.nodes:
            return self.nodes[n].get_num_pws()

        # Implicit Check
        is_sat = self.check_sat(constraints)
        if is_sat is not None:
            if is_sat:
                return 1, NumPWSType.atleast
            else:
                return 0, NumPWSType.exact

        # No idea based on current information
        return -1, NumPWSType.unevaluated

    def _check_node_ambiguity_(self, constraints):
        # explicit check in the self.nodes dict
        n = frozenset(constraints)
        if n in self.nodes:
            return self.nodes[n].is_ambiguous
        return None

    def check_ambiguity(self, n, mss_es: set=None, mus_es: set=None, mas_es: set=None, muas_es: set=None):
        """
        :param n:
        :param mss_es: Set of frozensets (each frozenset corresponds to an MSS)
        :param mus_es: Set of frozensets (each frozenset corresponds to an MUS)
        :param mas_es: Set of frozensets (each frozenset corresponds to an MAS)
        :param muas_es: Set of frozensets (each frozenset corresponds to an MUAS)
        :return:
        """

        # AMB if ancestor of an MAS or an MUAS
        # UNSAT if descendant of an MSS or an MUS

        # Explicit Check
        k = self._check_node_ambiguity_(n)
        if k is not None:
            return k

        if mss_es is None:
            mss_es = self.maximal_satisfiable_constraint_subsets
        if mus_es is None:
            mus_es = self.minimal_unsatisfiable_constraint_subsets
        if mas_es is None:
            mas_es = self.maximal_ambiguous_constraint_subsets
        if muas_es is None:
            muas_es = self.minimal_unambiguous_constraint_subsets

        n = set(n)

        # Implicit Checks

        for c in mas_es.union(muas_es):
            if n <= c:
                # AMB if ancestor of an MAS or an MUAS
                return NodeAmbiguityType.ambiguous

        for c in mus_es.union(mss_es):
            if n >= c:
                # UNAMB if descendant of an MSS or an MUS
                return NodeAmbiguityType.unsat

        return None

    def check_node_eval_state(self, constraints) -> NodeEvalState:

        # Explicit Check
        n = frozenset(constraints)
        if n in self.nodes:
            return self.nodes[n].eval_state

        # Implicit Checks
        is_sat = self.check_sat(constraints)
        if is_sat is not None:
            return NodeEvalState.evaluated

        return NodeEvalState.unevaluated

    def grow_ambiguous(self, seed, cnf_prog: CNFProgram, update_map_with_mas=True,
                       update_map_with_intermediate_results=True):
        seed = set(seed)
        iter_set = self.constraints_set - seed
        for c in list(iter_set):
            if cnf_prog.check_ambiguity(seed.union({c})) == NodeAmbiguityType.ambiguous:
                seed.add(c)
        if update_map_with_mas:
            self.maximal_ambiguous_constraint_subsets.add(seed)
        return seed

    def shrink_unambiguous(self, seed, cnf_prog: CNFProgram, update_map_with_muas=True,
                           update_map_with_intermediate_results=True):
        seed = set(seed)
        iter_set = seed.copy()
        for c in iter_set:
            if cnf_prog.check_ambiguity(seed.difference({c})) == NodeAmbiguityType.unambiguous:
                seed.remove(c)
        if update_map_with_muas:
            self.minimal_unambiguous_constraint_subsets.add(seed)
        return seed
