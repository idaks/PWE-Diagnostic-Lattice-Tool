class PowersetBitLib:

    @staticmethod
    def int_to_bitlist(num: int, num_bits: int) -> list:
        return [bool((num >> i) & 1) for i in range(num_bits - 1, -1, -1)]

    @staticmethod
    def bitlist_to_int(bitlist: list) -> int:
        out = 0
        for bit in bitlist:
            out = (out << 1) | bit
        return out

    @staticmethod
    def get_parents(num: int, num_constraints: int) -> list:

        parents = []
        for i in range(num_constraints - 1, -1, -1):
            bit = (num >> i) & 1
            if bit == 1:
                parents.append(num - (1 << i))
        return parents

    @staticmethod
    def get_children(num: int, num_constraints: int) -> list:

        children = []
        for i in range(num_constraints - 1, -1, -1):
            bit = (num >> i) & 1
            if bit == 0:
                children.append(num + (1 << i))
        return children

    @staticmethod
    def is_ancestor(n1: int, n2: int) -> bool:
        """
        is n1 an ancestor of n2
        NOTE: a node is its own ancestor
        """
        return (n1 & n2) == n1

    @staticmethod
    def is_descendant(n1: int, n2: int) -> bool:
        """
        is n1 a descendant of n2
        NOTE: a node is its own descendant
        """
        return PowersetBitLib.is_ancestor(n2, n1)

    @staticmethod
    def one_set_bit(n: int) -> bool:
        """
        Is n an integer power of 2, i.e. has exactly one bit set in its binary representation
        https://stackoverflow.com/questions/51094594/how-to-check-if-exactly-one-bit-is-set-in-an-int
        """
        return (n & (n - 1)) == 0

    @staticmethod
    def is_parent(n1: int, n2: int) -> bool:
        """is n1 parent of n2"""
        return (n2 > n1) and PowersetBitLib.one_set_bit(n2 ^ n1)

    @staticmethod
    def is_child(n1: int, n2: int) -> bool:
        return PowersetBitLib.is_parent(n2, n1)

    @staticmethod
    def get_descendants(n: int, num_cons: int) -> list:

        if num_cons == 1 and n == 0:
            return [0, 1]
        if num_cons == 1 and n == 1:
            return [1]

        descendants = []
        common = 0
        for i in range(num_cons - 1, -1, -1):
            bit = (n >> i) & 1
            if bit == 0:
                rec = PowersetBitLib.get_descendants(n & ((1 << i) - 1), i)
                descendants.extend([(common << (i + 1)) + (0 << i) + r for r in rec])
                descendants.extend([(common << (i + 1)) + (1 << i) + r for r in rec])
                break
            else:
                common = (common << 1) + 1
        return descendants if len(descendants) > 0 else [common]

    @staticmethod
    def get_ancestors(n: int, num_cons: int) -> list:
        """
        Get ancestors of n assuming num_cons number of constraints
        :param n: Node in power-set lattice to get ancestors of
        :param num_cons: Number of constraints in the system
        :return: List of ints corresponding to the ancestors of n, including n.
        """

        if num_cons == 1 and n == 0:
            return [0]
        if num_cons == 1 and n == 1:
            return [0, 1]

        ancestors = []
        for i in range(num_cons - 1, -1, -1):
            bit = (n >> i) & 1
            if bit == 1:
                rec = PowersetBitLib.get_ancestors(n & ((1 << i) - 1), i)
                ancestors.extend([(0 << i) + r for r in rec])
                ancestors.extend([(1 << i) + r for r in rec])
                break
        return ancestors if len(ancestors) > 0 else [0]

    @staticmethod
    def get_num_set_bits_hamming(n: int) -> int:
        """
        Hamming method to get number set bits in an integer
        :param n: integer to count number of set bits in
        :return: number of set bits in n counted using the hamming method
        """
        w = 0
        while n:
            w += 1
            n &= n - 1
        return w

    @staticmethod
    def get_num_set_bits(n: int) -> int:
        """
        Get number set bits in an integer using python's bin function
        :param n: integer to count number of set bits in
        :return: number of set bits in n
        """
        return bin(n)[2:].count('1')

    # Naive Way
    # @staticmethod
    # def get_num_set_bits2(n):
    #     w = 0
    #     while (n):
    #         w += n & 1
    #         n >>= 1
    #     return w
