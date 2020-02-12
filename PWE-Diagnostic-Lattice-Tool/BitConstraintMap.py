from .ConstraintMap import ConstraintMap
from .LogicProgram import LogicProgram
from .LatticeNode import (
    Node,
    NodeEvalState,
    NumPWSType,
    NodeAmbiguityType,
)
from collections import defaultdict
from iteration_utilities import first
from .PowersetBitLib import PowersetBitLib


class BitConstraintMap(ConstraintMap):

    def __init__(self, constraints):
        ConstraintMap.__init__(self, constraints)
        self.constraints_set = set(constraints)
        self.constraint_to_int_map = dict(zip(constraints, range(self.num_constraints)))
        self.unexplored_set = set(range(2 ** self.num_constraints))
        self.explored_set = set([])
        self.nodes = defaultdict(Node)

    def int_to_constraint_set(self, n):
        return [self.constraints[self.num_constraints - i - 1] for i in range(self.num_constraints - 1, -1, -1) if
                (((n >> i) & 1) == 1)]

    def constraint_set_to_int(self, cons_set):
        s = 0
        for c in cons_set:
            s += (1 << (self.num_constraints - self.constraint_to_int_map[c] - 1))
        return s

    def constraint_set_to_bitlist(self, cons_set):
        return PowersetBitLib.int_to_bitlist(self.constraint_set_to_int(cons_set), self.num_constraints)

    def bitlist_to_constraint_set(self, bitlist):
        return self.int_to_constraint_set(PowersetBitLib.bitlist_to_int(bitlist))

    def __constraints_to_int_helper__(self, constraints):
        if not isinstance(constraints, int):
            if isinstance(constraints, (list, set, frozenset)):
                return self.constraint_set_to_int(constraints)
            else:
                print("n is not of a supported type (int, list, set, frozenset).")
                return None
        return constraints

    def update_num_pws(self, constraints, num_pws, num_pws_eval_type: NumPWSType):

        self.nodes[self.__constraints_to_int_helper__(constraints)].update_num_pws(num_pws=num_pws,
                                                                                   num_pws_eval_type=num_pws_eval_type)

    def check_node_num_pws(self, constraints):

        n = self.__constraints_to_int_helper__(constraints)

        # Explicit Check
        if n in self.nodes:
            num_pws, num_pws_type = self.nodes[n].get_num_pws()
            if num_pws_type != NumPWSType.unevaluated:
                return num_pws, num_pws_type

        # Implicit Check
        is_sat = self._check_node_sat_implicit_(constraints)
        if is_sat is not None:
            if is_sat:
                return 1, NumPWSType.atleast
            else:
                return 0, NumPWSType.exact

        # No idea based on current information
        return -1, NumPWSType.unevaluated

    def check_node_eval_state(self, constraints) -> NodeEvalState:

        n = self.__constraints_to_int_helper__(constraints)
        # Explicit Check
        if n in self.nodes:
            return self.nodes[n].eval_state

        # Implicit Checks
        is_sat = self._check_node_sat_implicit_(n)
        if is_sat is not None:
            return NodeEvalState.evaluated

        return NodeEvalState.unevaluated

    def _check_node_sat_explicit_(self, constraints):
        n = self.__constraints_to_int_helper__(constraints)
        if n in self.nodes:
            return self.nodes[n].is_sat()
        return None

    def _check_node_sat_implicit_(self, constraints, mss_es: set=None, mus_es: set=None, mas_es: set=None,
                                  muas_es: set=None):
        """
        :param constraints:
        :param mss_es: Set of ints (each int corresponds to an MSS)
        :param mus_es: Set of ints (each int corresponds to an MUS)
        :param mas_es: Set of ints (each int corresponds to an MAS)
        :param muas_es: Set of ints (each int corresponds to an MUAS)
        :return: bool if can be inferred from the map, else None
        """

        # SAT if ancestor of an MUS or an MSS
        # UNSAT if descendant of an MUS or an MSS
        # SAT if ancestor of MUAS or MAS

        n = self.__constraints_to_int_helper__(constraints)

        if mss_es is None:
            mss_es = self.maximal_satisfiable_constraint_subsets
        else:
            mss_es = set(map(self.__constraints_to_int_helper__, mss_es))

        if mus_es is None:
            mus_es = self.minimal_unsatisfiable_constraint_subsets
        else:
            mus_es = set(map(self.__constraints_to_int_helper__, mus_es))

        if mas_es is None:
            mas_es = self.maximal_ambiguous_constraint_subsets
        else:
            mas_es = set(map(self.__constraints_to_int_helper__, mas_es))

        if muas_es is None:
            muas_es = self.minimal_unambiguous_constraint_subsets
        else:
            muas_es = set(map(self.__constraints_to_int_helper__, muas_es))

        for c in mus_es.union(mss_es):
            # Can optimize by doing the conversion of c to int here, so it's only converted if needed
            if PowersetBitLib.is_ancestor(n, c):
                return True
            elif PowersetBitLib.is_descendant(n, c):
                return False
        for c in muas_es.union(mas_es):
            # Can optimize by doing the conversion of c to int here, so it's only converted if needed
            if PowersetBitLib.is_ancestor(n, c):
                return True

        return None

    def check_sat(self, constraints):
        constraints = self.__constraints_to_int_helper__(constraints)
        k = self._check_node_sat_explicit_(constraints)
        if k is not None:
            return k

        return self._check_node_sat_implicit_(constraints)

    def _check_node_ambiguity_explicit_(self, constraints):
        # explicit check in the self.nodes dict
        n = self.__constraints_to_int_helper__(constraints)
        if n in self.nodes:
            return self.nodes[n].is_ambiguous()
        return None

    def _check_node_ambiguity_implicit_(self, constraints, mss_es: set = None, mus_es: set = None, mas_es: set = None,
                                        muas_es: set = None):
        """
        :param constraints:
        :param mss_es: Set of ints (each int corresponds to an MSS)
        :param mus_es: Set of ints (each int corresponds to an MUS)
        :param mas_es: Set of ints (each int corresponds to an MAS)
        :param muas_es: Set of ints (each int corresponds to an MUAS)
        :return: bool if can be inferred from the map, else None
        """

        # AMB if ancestor of an MAS or an MUAS
        # UNSAT if descendant of an MSS or an MUS

        n = self.__constraints_to_int_helper__(constraints)

        if mss_es is None:
            mss_es = self.maximal_satisfiable_constraint_subsets
        else:
            mss_es = set(map(self.__constraints_to_int_helper__, mss_es))

        if mus_es is None:
            mus_es = self.minimal_unsatisfiable_constraint_subsets
        else:
            mus_es = set(map(self.__constraints_to_int_helper__, mus_es))

        if mas_es is None:
            mas_es = self.maximal_ambiguous_constraint_subsets
        else:
            mas_es = set(map(self.__constraints_to_int_helper__, mas_es))

        if muas_es is None:
            muas_es = self.minimal_unambiguous_constraint_subsets
        else:
            muas_es = set(map(self.__constraints_to_int_helper__, muas_es))

        for c in mas_es.union(muas_es):
            # Can optimize by doing the conversion of c to int here, so it's only converted if needed
            if PowersetBitLib.is_ancestor(n, c):
                # AMB if ancestor of an MAS or an MUAS
                return NodeAmbiguityType.ambiguous

        for c in mus_es.union(mss_es):
            # Can optimize by doing the conversion of c to int here, so it's only converted if needed
            if PowersetBitLib.is_descendant(n, c):
                # UNSAT if descendant of an MSS or an MUS
                return NodeAmbiguityType.unsat

        return None

    def check_ambiguity(self, constraints):
        # Explicit Check
        constraints = self.__constraints_to_int_helper__(constraints)
        k = self._check_node_ambiguity_explicit_(constraints)
        if k is not None:
            return k
        return self._check_node_ambiguity_implicit_(constraints)

    def get_unexplored(self):
        if len(self.unexplored_set) <= 0:
            return None
        node = first(self.unexplored_set)
        return self.int_to_constraint_set(node)

    def get_unexplored_max(self):
        if len(self.unexplored_set) <= 0:
            return None
        return self.int_to_constraint_set(max(self.unexplored_set, key=PowersetBitLib.get_num_set_bits))

    def block_down(self, constraints, constraints_int: int=None):
        if constraints_int is None:
            constraints_int = self.constraint_set_to_int(constraints)
        ancestors = PowersetBitLib.get_ancestors(constraints_int, self.num_constraints)
        self.unexplored_set.difference_update(ancestors)
        self.explored_set.update(ancestors)

    def block_up(self, constraints, constraints_int: int=None):
        if constraints_int is None:
            constraints_int = self.constraint_set_to_int(constraints)
        descendants = PowersetBitLib.get_descendants(constraints_int, self.num_constraints)
        self.unexplored_set.difference_update(descendants)
        self.explored_set.update(descendants)

    def grow(self, seed, cnf_prog, seed_int: int=None, update_map_with_mss=True,
             update_map_with_intermediate_results=True, return_mss_int=False):

        seed = set(seed)
        if seed_int is None:
            seed_int = self.constraint_set_to_int(seed)  # Potential MSS

        n = seed_int
        for i in range(self.num_constraints - 1, -1, -1):
            bit = (n >> i) & 1
            if bit == 0:
                c = self.constraints[self.num_constraints - i - 1]
                seed_plus_c = seed.union({c})
                seed_plus_c_int = seed_int + (1 << i)

                memoized_result = self._check_node_sat_explicit_(seed_plus_c_int)
                if memoized_result is not None:
                    if memoized_result is True:
                        seed.add(c)
                        seed_int = seed_plus_c_int
                else:  # memoized_result is None:
                    sat_check = cnf_prog.check_sat(seed_plus_c)
                    if sat_check:
                        seed.add(c)
                        seed_int = seed_plus_c_int
                    if update_map_with_intermediate_results:
                        if sat_check is True:
                            self.update_num_pws(seed_plus_c_int, num_pws=1, num_pws_eval_type=NumPWSType.atleast)
                        else:  # if sat_check is False:
                            self.update_num_pws(seed_plus_c_int, num_pws=0, num_pws_eval_type=NumPWSType.exact)

        if update_map_with_mss:
            self.maximal_satisfiable_constraint_subsets.add(seed_int)

        if return_mss_int:
            return seed, seed_int
        return seed

    def shrink(self, seed, cnf_prog, seed_int: int=None, update_map_with_mus=True,
               update_map_with_intermediate_results=True, return_mus_int=False):
        seed = set(seed)

        if seed_int is None:
            seed_int = self.constraint_set_to_int(seed)  # Potential MUS

        n = seed_int
        for i in range(self.num_constraints - 1, -1, -1):
            bit = (n >> i) & 1
            if bit == 1:
                c = self.constraints[self.num_constraints - i - 1]

                seed_minus_c = seed.difference({c})
                seed_minus_c_int = seed_int - (1 << i)

                memoized_result = self._check_node_sat_explicit_(seed_minus_c_int)
                if memoized_result is not None:
                    if memoized_result is False:
                        seed.remove(c)
                        seed_int = seed_minus_c_int
                else:  # memoized_result is None:
                    sat_check = cnf_prog.check_sat(seed_minus_c)
                    if not sat_check:
                        seed.remove(c)
                        seed_int = seed_minus_c_int
                    if update_map_with_intermediate_results:
                        if sat_check is True:
                            self.update_num_pws(seed_minus_c_int, num_pws=1, num_pws_eval_type=NumPWSType.atleast)
                        else:  # if sat_check is False:
                            self.update_num_pws(seed_minus_c_int, num_pws=0, num_pws_eval_type=NumPWSType.exact)

        if update_map_with_mus:
            self.minimal_unsatisfiable_constraint_subsets.add(seed_int)

        if return_mus_int:
            return seed, seed_int
        return seed

    def grow_ambiguous(self, seed, cnf_prog: LogicProgram, seed_int: int=None, update_map_with_mas=True,
                       update_map_with_intermediate_results=True, return_mas_int=False):
        seed = set(seed)
        if seed_int is None:
            seed_int = self.constraint_set_to_int(seed)  # Potential MAS

        n = seed_int
        for i in range(self.num_constraints - 1, -1, -1):
            bit = (n >> i) & 1
            if bit == 0:
                c = self.constraints[self.num_constraints - i - 1]
                seed_plus_c = seed.union({c})
                seed_plus_c_int = seed_int + (1 << i)

                memoized_result = self._check_node_ambiguity_explicit_(seed_plus_c_int)
                if memoized_result is not None:
                    if memoized_result == NodeAmbiguityType.ambiguous:
                        seed.add(c)
                        seed_int = seed_plus_c_int
                else:  # memoized_result is None
                    amb_check = cnf_prog.check_ambiguity(seed_plus_c)
                    if amb_check == NodeAmbiguityType.ambiguous:
                        seed.add(c)
                        seed_int = seed_plus_c_int
                    if update_map_with_intermediate_results:
                        if amb_check == NodeAmbiguityType.ambiguous:
                            self.update_num_pws(seed_plus_c_int, num_pws=2, num_pws_eval_type=NumPWSType.atleast)
                        elif amb_check == NodeAmbiguityType.unambiguous:
                            self.update_num_pws(seed_plus_c_int, num_pws=1, num_pws_eval_type=NumPWSType.exact)
                        elif amb_check == NodeAmbiguityType.unsat:
                            self.update_num_pws(seed_plus_c_int, num_pws=0, num_pws_eval_type=NumPWSType.exact)

        if update_map_with_mas:
            self.maximal_ambiguous_constraint_subsets.add(seed_int)

        if return_mas_int:
            return seed, seed_int
        return seed

    def shrink_unambiguous(self, seed, cnf_prog: LogicProgram, seed_int: int=None, update_map_with_muas=True,
                           update_map_with_intermediate_results=True, return_muas_int=False):

        seed = set(seed)
        if seed_int is None:
            seed_int = self.constraint_set_to_int(seed)  # Potential MUAS

        n = seed_int
        for i in range(self.num_constraints - 1, -1, -1):
            bit = (n >> i) & 1
            if bit == 1:
                c = self.constraints[self.num_constraints - i - 1]
                seed_minus_c = seed.difference({c})
                seed_minus_c_int = seed_int - (1 << i)

                memoized_result = self._check_node_ambiguity_explicit_(seed_minus_c_int)
                if memoized_result is not None:
                    if memoized_result == NodeAmbiguityType.unambiguous:
                        seed.remove(c)
                        seed_int = seed_minus_c_int
                else:  # memoized_result is None
                    amb_check = cnf_prog.check_ambiguity(seed_minus_c)
                    if amb_check == NodeAmbiguityType.unambiguous:
                        seed.remove(c)
                        seed_int = seed_minus_c_int
                    if update_map_with_intermediate_results:
                        if amb_check == NodeAmbiguityType.ambiguous:
                            self.update_num_pws(seed_minus_c_int, num_pws=2, num_pws_eval_type=NumPWSType.atleast)
                        elif amb_check == NodeAmbiguityType.unambiguous:
                            self.update_num_pws(seed_minus_c_int, num_pws=1, num_pws_eval_type=NumPWSType.exact)
                        elif amb_check == NodeAmbiguityType.unsat:
                            self.update_num_pws(seed_minus_c_int, num_pws=0, num_pws_eval_type=NumPWSType.exact)

        if update_map_with_muas:
            self.minimal_unambiguous_constraint_subsets.add(seed_int)

        if return_muas_int:
            return seed, seed_int
        return seed
