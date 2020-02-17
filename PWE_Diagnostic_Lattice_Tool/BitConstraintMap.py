from .ConstraintMap import ConstraintMap
from .LogicProgram import LogicProgram
from .LatticeNode import (
    Node,
    NodeEvalState,
    NumPWSType,
    NodeAmbiguityType,
)
import itertools
import random
from .PowersetBitLib import PowersetBitLib


class BitConstraintMap(ConstraintMap):

    def __init__(self, constraints: list):
        ConstraintMap.__init__(self, constraints)
        self.constraints_set = set(constraints)
        self.constraint_to_int_map = dict(zip(constraints, range(self.num_constraints)))
        self.unexplored_set = set(range(2 ** self.num_constraints))
        self.explored_set = set([])
        self.satisfiable_set = set([])
        self.unsatisfiable_set = set([])
        self.ambiguous_set = set([])

    def reset_explored_set(self):
        self.unexplored_set = set(range(2 ** self.num_constraints))
        self.explored_set = set([])

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

    def _check_node_num_pws_explicit_(self, constraints, check_against_memoized_sets=True):

        n = self.__constraints_to_int_helper__(constraints)
        if n in self.nodes:
            num_pws, num_pws_type = self.nodes[n].get_num_pws()
            if num_pws_type != NumPWSType.unevaluated:
                return num_pws, num_pws_type

        if check_against_memoized_sets:
            if n in self.ambiguous_set:
                return 2, NumPWSType.atleast
            if n in self.satisfiable_set:
                return 1, NumPWSType.atleast
            if n in self.unsatisfiable_set:
                return 0, NumPWSType.exact
            if n in self.minimal_unambiguous_constraint_subsets:
                return 1, NumPWSType.exact

        return None, None

    def _check_node_num_pws_implicit_(self, constraints):

        n = self.__constraints_to_int_helper__(constraints)
        # is_sat = self._check_node_sat_implicit_(n)
        is_sat = self._check_node_sat_explicit_(n)
        if is_sat is not None:
            if is_sat:
                return 1, NumPWSType.atleast
            else:
                return 0, NumPWSType.exact
        return None, None

    def check_node_num_pws(self, constraints):

        n = self.__constraints_to_int_helper__(constraints)

        # Explicit Check
        explicit_check_result = self._check_node_num_pws_explicit_(n)
        if explicit_check_result[0] is not None:
            return explicit_check_result

        # Implicit Check
        implicit_check_result = self._check_node_num_pws_implicit_(n)
        if implicit_check_result[0] is not None:
            return implicit_check_result

        # No idea based on current information
        return -1, NumPWSType.unevaluated

    def check_node_eval_state(self, constraints) -> NodeEvalState:

        n = self.__constraints_to_int_helper__(constraints)
        # Explicit Check
        if n in self.nodes:
            return self.nodes[n].eval_state

        is_sat = self._check_node_sat_explicit_(n)
        if is_sat is not None:
            return NodeEvalState.evaluated

        # # Implicit Checks
        # is_sat = self._check_node_sat_implicit_(n)
        # if is_sat is not None:
        #     return NodeEvalState.evaluated

        return NodeEvalState.unevaluated

    def _check_node_sat_explicit_(self, constraints, check_against_memoized_sets=True):
        n = self.__constraints_to_int_helper__(constraints)

        if check_against_memoized_sets:
            if n in self.satisfiable_set:
                return True
            if n in self.unsatisfiable_set:
                return False

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

        # Necessary short circuiting since the for loops below only work assuming n is not in these sets
        # O/w for example if n == c and c is an MUS, n is an ancestor of c, but shouldn't be satisfiable
        if n in mus_es:
            return False
        if n in mss_es:
            return True
        if n in muas_es:
            return True
        if n in mas_es:
            return True

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
        # if k is not None:
        #     return k
        #
        # return self._check_node_sat_implicit_(constraints)
        return k

    def _check_node_ambiguity_explicit_(self, constraints, check_against_memoized_sets=True):
        # explicit check in the self.nodes dict
        n = self.__constraints_to_int_helper__(constraints)

        if check_against_memoized_sets:
            if n in self.ambiguous_set:
                return NodeAmbiguityType.ambiguous
            elif n in self.unsatisfiable_set:
                return NodeAmbiguityType.unsat

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

        if n in mas_es:
            return NodeAmbiguityType.ambiguous
        elif n in muas_es:
            return NodeAmbiguityType.unambiguous
        elif n in mus_es:
            return NodeAmbiguityType.unsat
        elif n in mss_es:
            return None

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
        # if k is not None:
        #     return k
        # return self._check_node_ambiguity_implicit_(constraints)
        return k

    def get_unexplored(self, return_seed_int=False):

        if len(self.unexplored_set) <= 0:
            if return_seed_int:
                return None, None
            return None

        node = random.sample(self.unexplored_set, 1)[0]
        if return_seed_int:
            return self.int_to_constraint_set(node), node
        return self.int_to_constraint_set(node)

    def get_unexplored_max(self, return_seed_int=False):

        if len(self.unexplored_set) <= 0:
            if return_seed_int:
                return None, None
            return None

        seed = max(self.unexplored_set, key=PowersetBitLib.get_num_set_bits)
        if return_seed_int:
            return self.int_to_constraint_set(seed), seed
        return self.int_to_constraint_set(seed)

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
                    else:
                        if update_map_with_intermediate_results:
                            self.update_num_pws(seed_plus_c_int, num_pws=0, num_pws_eval_type=NumPWSType.exact)

                    # if update_map_with_intermediate_results:
                    #     if sat_check is True:
                    #         # """Do we really need this case? If it is true,
                    #         #    it will become a ancestor of the eventual MSS"""
                    #         self.update_num_pws(seed_plus_c_int, num_pws=1, num_pws_eval_type=NumPWSType.atleast)
                    #     else:  # if sat_check is False:
                    #         self.update_num_pws(seed_plus_c_int, num_pws=0, num_pws_eval_type=NumPWSType.exact)

        if update_map_with_mss:
            self.maximal_satisfiable_constraint_subsets.add(seed_int)
            sat_ancestors = set(PowersetBitLib.get_ancestors(seed_int, self.num_constraints))
            unsat_descendants = set(PowersetBitLib.get_descendants(seed_int, self.num_constraints)).difference(
                {seed_int})
            self.satisfiable_set.update(sat_ancestors)
            self.unsatisfiable_set.update(unsat_descendants)

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
                    else:
                        if update_map_with_intermediate_results:
                            self.update_num_pws(seed_minus_c_int, num_pws=1, num_pws_eval_type=NumPWSType.atleast)

                    # if update_map_with_intermediate_results:
                    #     if sat_check is True:
                    #         self.update_num_pws(seed_minus_c_int, num_pws=1, num_pws_eval_type=NumPWSType.atleast)
                    #     else:  # if sat_check is False:
                    #         self.update_num_pws(seed_minus_c_int, num_pws=0, num_pws_eval_type=NumPWSType.exact)

        if update_map_with_mus:
            self.minimal_unsatisfiable_constraint_subsets.add(seed_int)
            sat_ancestors = set(PowersetBitLib.get_ancestors(seed_int, self.num_constraints)).difference({seed_int})
            unsat_descendants = set(PowersetBitLib.get_descendants(seed_int, self.num_constraints))
            self.satisfiable_set.update(sat_ancestors)
            self.unsatisfiable_set.update(unsat_descendants)

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
                    else:
                        if update_map_with_intermediate_results:
                            if amb_check == NodeAmbiguityType.unambiguous:
                                self.update_num_pws(seed_plus_c_int, num_pws=1, num_pws_eval_type=NumPWSType.exact)
                            elif amb_check == NodeAmbiguityType.unsat:
                                self.update_num_pws(seed_plus_c_int, num_pws=0, num_pws_eval_type=NumPWSType.exact)

                    # if update_map_with_intermediate_results:
                    #     if amb_check == NodeAmbiguityType.ambiguous:
                    #         self.update_num_pws(seed_plus_c_int, num_pws=2, num_pws_eval_type=NumPWSType.atleast)
                    #     elif amb_check == NodeAmbiguityType.unambiguous:
                    #         self.update_num_pws(seed_plus_c_int, num_pws=1, num_pws_eval_type=NumPWSType.exact)
                    #     elif amb_check == NodeAmbiguityType.unsat:
                    #         self.update_num_pws(seed_plus_c_int, num_pws=0, num_pws_eval_type=NumPWSType.exact)

        if update_map_with_mas:
            self.maximal_ambiguous_constraint_subsets.add(seed_int)
            amb_ancestors = set(PowersetBitLib.get_ancestors(seed_int, self.num_constraints))
            self.ambiguous_set.update(amb_ancestors)
            self.satisfiable_set.update(amb_ancestors)

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

                    # Keep in this case because the blocked sections are a mix of UNAMB (==1PW) and UNSAT,
                    # so this information is still useful
                    if update_map_with_intermediate_results:
                        if amb_check == NodeAmbiguityType.ambiguous:
                            self.update_num_pws(seed_minus_c_int, num_pws=2, num_pws_eval_type=NumPWSType.atleast)
                        elif amb_check == NodeAmbiguityType.unambiguous:
                            self.update_num_pws(seed_minus_c_int, num_pws=1, num_pws_eval_type=NumPWSType.exact)
                        elif amb_check == NodeAmbiguityType.unsat:
                            self.update_num_pws(seed_minus_c_int, num_pws=0, num_pws_eval_type=NumPWSType.exact)

        if update_map_with_muas:
            self.minimal_unambiguous_constraint_subsets.add(seed_int)
            amb_ancestors = set(PowersetBitLib.get_ancestors(seed_int, self.num_constraints)).difference({seed_int})
            self.ambiguous_set.update(amb_ancestors)
            self.satisfiable_set.update(amb_ancestors)
            self.satisfiable_set.add(seed_int)

        if return_muas_int:
            return seed, seed_int
        return seed

    def get_all_nodes_num_pws(self):

        num_pws = {k: (None, None) for k in range(2**self.num_constraints)}

        for n in self.satisfiable_set.difference(self.ambiguous_set):
            explicit_check = self._check_node_num_pws_explicit_(n, check_against_memoized_sets=False)
            num_pws[n] = explicit_check if explicit_check[0] is not None else (1, NumPWSType.atleast)
        for n in self.unsatisfiable_set:
            num_pws[n] = (0, NumPWSType.exact)
        for n in self.ambiguous_set:
            explicit_check = self._check_node_num_pws_explicit_(n, check_against_memoized_sets=False)
            if explicit_check[0] is not None:
                if explicit_check[1] == NumPWSType.atleast:
                    num_pws[n] = (max(2, explicit_check[0]), NumPWSType.atleast)
                elif explicit_check[1] == NumPWSType.exact:
                    num_pws[n] = explicit_check
                elif explicit_check[1] == NumPWSType.unevaluated:
                    num_pws[n] = (2, NumPWSType.atleast)
            else:
                num_pws[n] = (2, NumPWSType.atleast)
        for n in self.minimal_unambiguous_constraint_subsets:
            num_pws[n] = (1, NumPWSType.exact)

        pot_missed_nodes = set(itertools.chain.from_iterable(
            PowersetBitLib.get_descendants(n, self.num_constraints) for n in self.minimal_unambiguous_constraint_subsets)
        ).difference(self.minimal_unambiguous_constraint_subsets)\
            .difference(self.satisfiable_set)\
            .difference(self.unsatisfiable_set)

        unexplored = self.unexplored_set.union(pot_missed_nodes)
        for n in unexplored:
            num_pws[n] = self._check_node_num_pws_explicit_(n, check_against_memoized_sets=False)

        return num_pws

    def get_all_nodes_sat(self):

        node_to_sat = {k: None for k in range(2**self.num_constraints)}

        for n in self.satisfiable_set:
            node_to_sat[n] = True
        for n in self.unsatisfiable_set:
            node_to_sat[n] = False
        for n in node_to_sat.keys():
            if node_to_sat[n] is None:
                node_to_sat[n] = self._check_node_sat_explicit_(n, check_against_memoized_sets=False)

        return node_to_sat

    # TODO
    def get_all_nodes_ambiguity_status(self):
        pass







