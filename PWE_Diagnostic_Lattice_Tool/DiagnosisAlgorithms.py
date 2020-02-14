from .ConstraintMap import ConstraintMap
from .BitConstraintMap import BitConstraintMap
from .LogicProgram import LogicProgram
from .LatticeNode import NodeAmbiguityType
import numpy as np


class DiagnosisAlgorithmsHelpers:

    @staticmethod
    def check_sat(seed, cmap: ConstraintMap, cnf_prog: LogicProgram):
        """
        First check against cmap if seed is SAT, if cannot be inferred from available info, then determine using the
        cnf_prog
        :param seed: Set of constraints
        :param cmap: ConstraintMap Object
        :param cnf_prog: LogicProgram Object
        :return: bool
        """
        cmap_inference = cmap.check_sat(constraints=seed)
        if cmap_inference is not None:
            return cmap_inference
        return cnf_prog.check_sat(constraints=seed)

    @staticmethod
    def check_sat_bit_optimized(seed, cmap: BitConstraintMap, cnf_prog: LogicProgram, seed_int: int=None):
        """
        First check against cmap if seed is SAT, if cannot be inferred from available info, then determine using the
        cnf_prog.
        Optimized for BitConstraintMaps (if seed_int is provided)
        :param seed: Set of constraints
        :param cmap: ConstraintMap Object
        :param cnf_prog: LogicProgram Object
        :param seed_int: Int representation of seed
        :return: bool
        """
        cmap_inference = (cmap.check_sat(constraints=seed_int)) if (seed_int is not None) \
            else (cmap.check_sat(constraints=seed))

        if cmap_inference is not None:
            return cmap_inference
        return cnf_prog.check_sat(constraints=seed)

    @staticmethod
    def check_ambiguity(seed, cmap: ConstraintMap, cnf_prog: LogicProgram):
        """
        First check against cmap if seed is AMBIGUOUS, if cannot be inferred from available info, then determine using
        the cnf_prog
        :param seed: Set of constraints
        :param cmap: ConstraintMap Object
        :param cnf_prog: LogicProgram Object
        :return: bool
        """
        cmap_inference = cmap.check_ambiguity(constraints=seed)
        if cmap_inference is not None:
            return cmap_inference
        return cnf_prog.check_ambiguity(constraints=seed)

    @staticmethod
    def check_ambiguity_bit_optimized(seed, cmap: BitConstraintMap, cnf_prog: LogicProgram, seed_int: int=None):
        """
        First check against cmap if seed is AMBIGUOUS, if cannot be inferred from available info, then determine using
        the cnf_prog.
        Optimized for BitConstraintMaps (if seed_int is provided)
        :param seed: Set of constraints
        :param cmap: ConstraintMap Object
        :param cnf_prog: LogicProgram Object
        :param seed_int: Int representation of seed
        :return: bool
        """
        cmap_inference = (cmap.check_ambiguity(constraints=seed_int)) if (seed_int is not None) \
            else (cmap.check_ambiguity(constraints=seed))
        if cmap_inference is not None:
            return cmap_inference
        return cnf_prog.check_ambiguity(constraints=seed)


class DiagnosisAlgorithms:

    @staticmethod
    def marco(cmap: ConstraintMap, cnf_prog: LogicProgram, min_mss_to_find=np.infty, min_mus_to_find=np.infty):
        """
        To get the Minimal Unsatisfiable Constraint Subsets (MUSes) and Maximal Consistent Constraint Subsets (MSSes).
        Will stop after finding min_mss_to_find MSSes and min_mus_to_find MUSes, if these many exist.
        Stops once the map has been completely explored.
        Based on: Fast, Flexible MUS Enumeration by Liffiton et. al.
        (https://sun.iwu.edu/~mliffito/marco/)
        :param cmap: A ConstraintMap object to explore
        :param cnf_prog: A LogicProgram to find the MSSes and MUSes for
        :param min_mss_to_find: Minimum number of MSSes to find. (default: infinity i.e. all)
        :param min_mus_to_find: Minimum number of MUSes to find. (default: infinity i.e. all)
        :return: (MUSes, MSSes) : both are lists, containing sets of constraint subsets
        """

        mus_es = []
        mss_es = []

        seed = cmap.get_unexplored()
        while (seed is not None) and ((len(mus_es) < min_mus_to_find) or (len(mss_es) < min_mss_to_find)):

            if DiagnosisAlgorithmsHelpers.check_sat(seed=seed, cmap=cmap, cnf_prog=cnf_prog):
                mss = cmap.grow(seed, cnf_prog)
                mss_es.append(mss)
                cmap.block_down(mss)
            else:  # if UNSATISFIABLE
                mus = cmap.shrink(seed, cnf_prog)
                mus_es.append(mus)
                cmap.block_up(mus)

            seed = cmap.get_unexplored()

        return mus_es, mss_es

    @staticmethod
    def marco_bit_optimized(cmap: BitConstraintMap, cnf_prog: LogicProgram, min_mss_to_find=np.infty,
                            min_mus_to_find=np.infty):
        """
        Bit optimized version of the MARCO algorithm.
        To get the Minimal Unsatisfiable Constraint Subsets (MUSes) and Maximal Consistent Constraint Subsets (MSSes).
        Will stop after finding min_mss_to_find MSSes and min_mus_to_find MUSes, if these many exist.
        Stops once the map has been completely explored.
        Based on: Fast, Flexible MUS Enumeration by Liffiton et. al.
        (https://sun.iwu.edu/~mliffito/marco/)
        :param cmap: A ConstraintMap object to explore
        :param cnf_prog: A LogicProgram to find the MSSes and MUSes for
        :param min_mss_to_find: Minimum number of MSSes to find. (default: infinity i.e. all)
        :param min_mus_to_find: Minimum number of MUSes to find. (default: infinity i.e. all)
        :return: (MUSes, MSSes) : both are lists, containing sets of constraint subsets
        """

        mus_es = []
        mss_es = []

        seed, seed_int = cmap.get_unexplored(return_seed_int=True)  # OPT1
        while (seed is not None) and ((len(mus_es) < min_mus_to_find) or (len(mss_es) < min_mss_to_find)):

            if DiagnosisAlgorithmsHelpers.check_sat_bit_optimized(seed=seed, seed_int=seed_int, cmap=cmap,
                                                                  cnf_prog=cnf_prog):
                mss, mss_int = cmap.grow(seed=seed, cnf_prog=cnf_prog, seed_int=seed_int, return_mss_int=True)  # OPT2
                mss_es.append(mss)
                cmap.block_down(constraints=mss, constraints_int=mss_int)  # OPT3
            else:  # if UNSATISFIABLE
                mus, mus_int = cmap.shrink(seed=seed, cnf_prog=cnf_prog, seed_int=seed_int, return_mus_int=True)  # OPT2
                mus_es.append(mus)
                cmap.block_up(constraints=mus, constraints_int=mus_int)  # OPT3

            seed, seed_int = cmap.get_unexplored(return_seed_int=True)  # OPT1

        return mus_es, mss_es

    @staticmethod
    def marco_plus(cmap: ConstraintMap, cnf_prog: LogicProgram, min_mss_to_find=np.infty, min_mus_to_find=np.infty):
        """
        To get the Minimal Unsatisfiable Constraint Subsets (MUSes) and Maximal Consistent Constraint Subsets (MSSes).
        This algorithm is best for finding few MSSes, since it tries biggest subsets first.
        Will stop after finding min_mss_to_find MSSes and min_mus_to_find MUSes, if these many exist.
        Stops once the map has been completely explored.
        Based on: Fast, Flexible MUS Enumeration by Liffiton et. al.
        (https://sun.iwu.edu/~mliffito/marco/)
        :param cmap: A ConstraintMap object to explore
        :param cnf_prog: A LogicProgram to find the MSSes and MUSes for
        :param min_mss_to_find: Minimum number of MSSes to find. (default: infinity i.e. all)
        :param min_mus_to_find: Minimum number of MUSes to find. (default: infinity i.e. all)
        :return: (MUSes, MSSes) : both are lists, containing sets of constraint subsets
        """

        mus_es = []
        mss_es = []

        seed = cmap.get_unexplored_max()
        while (seed is not None) and ((len(mus_es) < min_mus_to_find) or (len(mss_es) < min_mss_to_find)):

            if DiagnosisAlgorithmsHelpers.check_sat(seed=seed, cmap=cmap, cnf_prog=cnf_prog):
                mss = seed
                mss_es.append(mss)
                cmap.block_down(mss)
            else:  # if Unsatisfiable
                mus = cmap.shrink(seed, cnf_prog)
                mus_es.append(mus)
                cmap.block_up(mus)

            seed = cmap.get_unexplored_max()

        return mus_es, mss_es

    @staticmethod
    def marco_plus_bit_optimized(cmap: BitConstraintMap, cnf_prog: LogicProgram, min_mss_to_find=np.infty,
                                 min_mus_to_find=np.infty):
        """
        Bit optimized version of the MARCO PLUS algorithm.
        To get the Minimal Unsatisfiable Constraint Subsets (MUSes) and Maximal Consistent Constraint Subsets (MSSes).
        This algorithm is best for finding few MSSes, since it tries biggest subsets first.
        Will stop after finding min_mss_to_find MSSes and min_mus_to_find MUSes, if these many exist.
        Stops once the map has been completely explored.
        Based on: Fast, Flexible MUS Enumeration by Liffiton et. al.
        (https://sun.iwu.edu/~mliffito/marco/)
        :param cmap: A ConstraintMap object to explore
        :param cnf_prog: A LogicProgram to find the MSSes and MUSes for
        :param min_mss_to_find: Minimum number of MSSes to find. (default: infinity i.e. all)
        :param min_mus_to_find: Minimum number of MUSes to find. (default: infinity i.e. all)
        :return: (MUSes, MSSes) : both are lists, containing sets of constraint subsets
        """

        mus_es = []
        mss_es = []

        seed, seed_int = cmap.get_unexplored_max(return_seed_int=True)  # OPT1
        while (seed is not None) and ((len(mus_es) < min_mus_to_find) or (len(mss_es) < min_mss_to_find)):

            if DiagnosisAlgorithmsHelpers.check_sat_bit_optimized(seed=seed, seed_int=seed_int, cmap=cmap,
                                                                  cnf_prog=cnf_prog):
                mss, mss_int = seed, seed_int  # OPT2
                mss_es.append(mss)
                cmap.block_down(constraints=mss, constraints_int=mss_int)  # OPT3
            else:  # if Unsatisfiable
                mus, mus_int = cmap.shrink(seed=seed, cnf_prog=cnf_prog, seed_int=seed_int, return_mus_int=True)  # OPT2
                mus_es.append(mus)
                cmap.block_up(constraints=mus, constraints_int=mus_int)  # OPT3

            seed, seed_int = cmap.get_unexplored_max(return_seed_int=True)  # OPT1

        return mus_es, mss_es

    @staticmethod
    def marco_ambiguous(cmap: ConstraintMap, cnf_prog: LogicProgram, min_mas_to_find=np.infty,
                        min_muas_to_find=np.infty):
        """
        To get the Minimal Unambiguous Constraint Subsets (MUASes) and Maximal Ambiguous Constraint Subsets (MASes).
        MUAS: Set of constraints such that they produce a unique solution and removing any constraints would
        increase the number of solutions.
        MAS: Set of constraints such that they have multiple (> 1) solutions and adding any constraint would
        make it either unambiguous (unique solution) or unsatisfiable (no solution)
        Will stop after finding min_mas_to_find MASes and min_muas_to_find MUASes, if these many exist.
        Stops once the map has been completely explored.
        Based on the algorithm in: Fast, Flexible MUS Enumeration by Liffiton et. al.
        (https://sun.iwu.edu/~mliffito/marco/)
        :param cmap: A ConstraintMap object to explore
        :param cnf_prog: A LogicProgram to find the MSSes and MUSes for
        :param min_mas_to_find: Minimum number of MASes to find. (default: infinity i.e. all)
        :param min_muas_to_find: Minimum number of MUASes to find. (default: infinity i.e. all)
        :return: (MUASes, MASes) : both are lists, containing sets of constraint subsets
        """

        muas_es = []  # Minimal Unambiguous Subsets
        mas_es = []   # Maximal Ambiguous Subsets

        seed = cmap.get_unexplored()
        while (seed is not None) and ((len(muas_es) < min_muas_to_find) or (len(mas_es) < min_mas_to_find)):

            amb_check = DiagnosisAlgorithmsHelpers.check_ambiguity(seed=seed, cmap=cmap, cnf_prog=cnf_prog)

            if amb_check == NodeAmbiguityType.unambiguous:
                muas = cmap.shrink_unambiguous(seed, cnf_prog)
                muas_es.append(muas)
                cmap.block_up(muas)
            elif amb_check == NodeAmbiguityType.ambiguous:
                mas = cmap.grow_ambiguous(seed, cnf_prog)
                mas_es.append(mas)
                cmap.block_down(mas)
            else:  # amb_check == NodeAmbiguityType.unsat
                mus = cmap.shrink(seed, cnf_prog)
                cmap.block_up(mus)

            seed = cmap.get_unexplored()

        return muas_es, mas_es

    @staticmethod
    def marco_ambiguous_bit_optimized(cmap: BitConstraintMap, cnf_prog: LogicProgram, min_mas_to_find=np.infty,
                                      min_muas_to_find=np.infty):
        """
        Bit optimized version of the MARCO AMBIGUOUS algorithm.
        To get the Minimal Unambiguous Constraint Subsets (MUASes) and Maximal Ambiguous Constraint Subsets (MASes).
        MUAS: Set of constraints such that they produce a unique solution and removing any constraints would
        increase the number of solutions.
        MAS: Set of constraints such that they have multiple (> 1) solutions and adding any constraint would
        make it either unambiguous (unique solution) or unsatisfiable (no solution)
        Will stop after finding min_mas_to_find MASes and min_muas_to_find MUASes, if these many exist.
        Stops once the map has been completely explored.
        Based on the algorithm in: Fast, Flexible MUS Enumeration by Liffiton et. al.
        (https://sun.iwu.edu/~mliffito/marco/)
        :param cmap: A ConstraintMap object to explore
        :param cnf_prog: A LogicProgram to find the MSSes and MUSes for
        :param min_mas_to_find: Minimum number of MASes to find. (default: infinity i.e. all)
        :param min_muas_to_find: Minimum number of MUASes to find. (default: infinity i.e. all)
        :return: (MUASes, MASes) : both are lists, containing sets of constraint subsets
        """

        muas_es = []  # Minimal Unambiguous Subsets
        mas_es = []   # Maximal Ambiguous Subsets

        seed, seed_int = cmap.get_unexplored(return_seed_int=True)  # OPT1
        while (seed is not None) and ((len(muas_es) < min_muas_to_find) or (len(mas_es) < min_mas_to_find)):

            amb_check = DiagnosisAlgorithmsHelpers.check_ambiguity_bit_optimized(seed=seed, seed_int=seed_int,
                                                                                 cmap=cmap, cnf_prog=cnf_prog)

            if amb_check == NodeAmbiguityType.unambiguous:
                # OPT2
                muas, muas_int = cmap.shrink_unambiguous(seed, cnf_prog, seed_int=seed_int, return_muas_int=True)
                muas_es.append(muas)
                cmap.block_up(constraints=muas, constraints_int=muas_int)  # OPT3
            elif amb_check == NodeAmbiguityType.ambiguous:
                mas, mas_int = cmap.grow_ambiguous(seed, cnf_prog, seed_int=seed_int, return_mas_int=True)  # OPT2
                mas_es.append(mas)
                cmap.block_down(constraints=mas, constraints_int=mas_int)  # OPT3
            else:  # amb_check == NodeAmbiguityType.unsat
                mus, mus_int = cmap.shrink(seed, cnf_prog, seed_int=seed_int, return_mus_int=True)  # OPT2
                cmap.block_up(constraints=mus, constraints_int=mus_int)  # OPT3

            seed, seed_int = cmap.get_unexplored(return_seed_int=True)  # OPT1

        return muas_es, mas_es

    @staticmethod
    def marco_ambiguous_plus(cmap: ConstraintMap, cnf_prog: LogicProgram, min_mas_to_find=np.infty,
                             min_muas_to_find=np.infty):
        """
        To get the Minimal Unambiguous Constraint Subsets (MUASes) and Maximal Ambiguous Constraint Subsets (MASes).
        This algorithm is best for finding few MASes, since it tries biggest subsets first.
        MUAS: Set of constraints such that they produce a unique solution and removing any constraints would
        increase the number of solutions.
        MAS: Set of constraints such that they have multiple (> 1) solutions and adding any constraint would
        make it either unambiguous (unique solution) or unsatisfiable (no solution)
        Will stop after finding min_mas_to_find MASes and min_muas_to_find MUASes, if these many exist.
        Stops once the map has been completely explored.
        Based on the algorithm in: Fast, Flexible MUS Enumeration by Liffiton et. al.
        (https://sun.iwu.edu/~mliffito/marco/)
        :param cmap: A ConstraintMap object to explore
        :param cnf_prog: A LogicProgram to find the MSSes and MUSes for
        :param min_mas_to_find: Minimum number of MASes to find. (default: infinity i.e. all)
        :param min_muas_to_find: Minimum number of MUASes to find. (default: infinity i.e. all)
        :return: (MUASes, MASes) : both are lists, containing sets of constraint subsets
        """

        muas_es = []  # Minimal Unambiguous Subsets
        mas_es = []  # Maximal Ambiguous Subsets

        seed = cmap.get_unexplored_max()
        while (seed is not None) and ((len(muas_es) < min_muas_to_find) or (len(mas_es) < min_mas_to_find)):

            amb_check = DiagnosisAlgorithmsHelpers.check_ambiguity(seed=seed, cmap=cmap, cnf_prog=cnf_prog)

            if amb_check == NodeAmbiguityType.unambiguous:
                muas = cmap.shrink_unambiguous(seed, cnf_prog)
                muas_es.append(muas)
                cmap.block_up(muas)
            elif amb_check == NodeAmbiguityType.ambiguous:
                mas = seed
                mas_es.append(mas)
                cmap.block_down(mas)
            else:  # amb_check == NodeAmbiguityType.unsat
                mus = cmap.shrink(seed, cnf_prog)
                cmap.block_up(mus)

            seed = cmap.get_unexplored_max()

        return muas_es, mas_es

    @staticmethod
    def marco_ambiguous_plus_bit_optimized(cmap: BitConstraintMap, cnf_prog: LogicProgram, min_mas_to_find=np.infty,
                                           min_muas_to_find=np.infty):
        """
        Bit optimized version of the MARCO AMBIGUOUS PLUS algorithm.
        To get the Minimal Unambiguous Constraint Subsets (MUASes) and Maximal Ambiguous Constraint Subsets (MASes).
        This algorithm is best for finding few MASes, since it tries biggest subsets first.
        MUAS: Set of constraints such that they produce a unique solution and removing any constraints would
        increase the number of solutions.
        MAS: Set of constraints such that they have multiple (> 1) solutions and adding any constraint would
        make it either unambiguous (unique solution) or unsatisfiable (no solution)
        Will stop after finding min_mas_to_find MASes and min_muas_to_find MUASes, if these many exist.
        Stops once the map has been completely explored.
        Based on the algorithm in: Fast, Flexible MUS Enumeration by Liffiton et. al.
        (https://sun.iwu.edu/~mliffito/marco/)
        :param cmap: A ConstraintMap object to explore
        :param cnf_prog: A LogicProgram to find the MSSes and MUSes for
        :param min_mas_to_find: Minimum number of MASes to find. (default: infinity i.e. all)
        :param min_muas_to_find: Minimum number of MUASes to find. (default: infinity i.e. all)
        :return: (MUASes, MASes) : both are lists, containing sets of constraint subsets
        """

        muas_es = []  # Minimal Unambiguous Subsets
        mas_es = []  # Maximal Ambiguous Subsets

        seed, seed_int = cmap.get_unexplored_max(return_seed_int=True)  # OPT1
        while (seed is not None) and ((len(muas_es) < min_muas_to_find) or (len(mas_es) < min_mas_to_find)):

            amb_check = DiagnosisAlgorithmsHelpers.check_ambiguity_bit_optimized(seed=seed, seed_int=seed_int,
                                                                                 cmap=cmap, cnf_prog=cnf_prog)

            if amb_check == NodeAmbiguityType.unambiguous:
                # OPT2
                muas, muas_int = cmap.shrink_unambiguous(seed, cnf_prog, seed_int=seed_int, return_muas_int=True)
                muas_es.append(muas)
                cmap.block_up(constraints=muas, constraints_int=muas_int)  # OPT3
            elif amb_check == NodeAmbiguityType.ambiguous:
                mas, mas_int = seed, seed_int  # OPT2
                mas_es.append(mas)
                cmap.block_down(constraints=mas, constraints_int=mas_int)  # OPT3
            else:  # amb_check == NodeAmbiguityType.unsat
                mus, mus_int = cmap.shrink(seed, cnf_prog, seed_int=seed_int, return_mus_int=True)  # OPT2
                cmap.block_up(constraints=mus, constraints_int=mus_int)  # OPT3

            seed, seed_int = cmap.get_unexplored_max(return_seed_int=True)  # OPT1

        return muas_es, mas_es
