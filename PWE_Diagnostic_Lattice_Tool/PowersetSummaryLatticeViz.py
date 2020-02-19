from .BitConstraintMap import BitConstraintMap
from .PowersetBitLib import PowersetBitLib
from .LatticeNode import NumPWSType
import networkx as nx


class PowersetSummaryLatticeViz:

    DEFAULT_COLOR_SCHEME = {
        'sat_node': {
            'colorscheme': 'paired12',
            'style': 'filled',
            'color': 3,
            'fillcolor': 3,
        },
        'unsat_node': {
            'colorscheme': 'paired12',
            'style': 'filled',
            'color': 5,
            'fillcolor': 5,
        },
        'mss_node': {
            'colorscheme': 'paired12',
            'style': 'filled',
            'color': 4,
            'fillcolor': 4,
        },
        'mus_node': {
            'colorscheme': 'paired12',
            'style': 'filled',
            'color': 6,
            'fillcolor': 6,
        },
        'muas_node': {
            'colorscheme': 'paired12',
            'style': 'filled',
            'color': 8,
            'fillcolor': 8,
        },
        'mas_node': {
            'colorscheme': 'paired12',
            'style': 'filled',
            'color': 12,
            'fillcolor': 12,
        },
        'unevaluated_node': {
            'colorscheme': 'paired12',
            'style': 'filled',
            'color': 11,
            'fillcolor': 11,
        },
        'sat_sat_edge': {
            'arrowhead': 'none',
            'colorscheme': 'paired12',
            'color': 3,
        },
        'sat_unsat_edge': {
            'arrowhead': 'none',
            'colorscheme': 'paired12',
            'color': 2,
        },
        'unsat_unsat_edge': {
            'arrowhead': 'none',
            'colorscheme': 'paired12',
            'color': 5,
        },
        'unevaluated_edge': {
            'arrowhead': 'none',
            'colorscheme': 'paired12',
            'color': 9,
        },
    }

    def __init__(self, cmap: BitConstraintMap):
        self.cmap = cmap
        self.summary_lattice = None
        self.lattice_nodes = set([])
        self.reset_lattice()
        self.mus_es = set([])
        self.mss_es = set([])
        self.muas_es = set([])
        self.mas_es = set([])
        self.null_node = 0
        self.all_node = 2 ** self.cmap.num_constraints - 1
        self.num_pws = {}
        self.num_set_bits = {}
        self.sat_status = {}
        self.resync_lattice()

    def reset_lattice(self):
        self.summary_lattice = nx.Graph()
        self.lattice_nodes = set([])

    def resync_lattice(self):

        self.mus_es = self.cmap.minimal_unsatisfiable_constraint_subsets
        self.mss_es = self.cmap.maximal_satisfiable_constraint_subsets
        self.muas_es = self.cmap.minimal_unambiguous_constraint_subsets
        self.mas_es = self.cmap.maximal_ambiguous_constraint_subsets
        pot_nodes = self.mus_es.union(self.mss_es).union(self.muas_es).union(self.mas_es).union({self.null_node,
                                                                                                 self.all_node})
        self.num_pws = {n: self.cmap.check_node_num_pws(n) for n in pot_nodes}
        self.num_set_bits = {n: PowersetBitLib.get_num_set_bits(n) for n in pot_nodes}
        self.sat_status = {n: self.cmap.check_sat(n) for n in pot_nodes}

    def get_node_label(self, n, label_format='bitstring', display_num_pws=False):

        def num_pws_to_str(num_pws: int, num_pws_type: NumPWSType):
            if num_pws is None:
                return "?"
            elif num_pws_type == NumPWSType.unevaluated:
                return "?"
            elif num_pws_type == NumPWSType.exact:
                return str(num_pws)
            elif num_pws_type == NumPWSType.atleast:
                return ">= {}".format(str(num_pws))

        label_format_to_func = {
            'bitstring': lambda x: self.int_to_bit_string(x),
            'int': lambda x: str(x),
            'comp_string': lambda x: "{{{}}}".format(", ".join(self.cmap.int_to_constraint_set(x))),
        }

        label = label_format_to_func[label_format](n)
        if display_num_pws:
            label += '\n({})'.format(num_pws_to_str(*self.num_pws[n]))

        return label

    def get_edge_style(self, e, colorscheme=None):

        e1, e2 = e

        if colorscheme is None:
            colorscheme = self.DEFAULT_COLOR_SCHEME

        if (self.sat_status[e1] is None) or (self.sat_status[e2] is None):
            return colorscheme['unevaluated_edge']
        if self.sat_status[e1] != self.sat_status[e2]:
            return colorscheme['sat_unsat_edge']
        if self.sat_status[e1] is True:
            return colorscheme['sat_sat_edge']
        if self.sat_status[e1] is False:
            return colorscheme['unsat_unsat_edge']

        return colorscheme['unevaluated_edge']

    def get_node_style(self, node, colorscheme=None):

        if colorscheme is None:
            colorscheme = self.DEFAULT_COLOR_SCHEME

        if node in self.mus_es:
            return colorscheme['mus_node']
        if node in self.mss_es:
            return colorscheme['mss_node']
        if self.num_pws[node][0] is not None:
            if self.num_pws[node][1] == NumPWSType.unevaluated:
                return colorscheme['unevaluated_node']
            if self.num_pws[node][1] == NumPWSType.exact:
                return colorscheme['sat_node'] if self.num_pws[node][0] > 0 else colorscheme['unsat_node']
            if self.num_pws[node][1] == NumPWSType.atleast:
                return colorscheme['sat_node'] if self.num_pws[node][0] > 0 else colorscheme['unevaluated_node']

        return colorscheme['unevaluated_node']

    def int_to_bit_string(self, num):
        return "".join(['1' if c else '0' for c in PowersetBitLib.int_to_bitlist(num, self.cmap.num_constraints)])

    def get_lattice(self, to_highlight=('MUS', 'MSS'), label_format='bitstring', display_num_pws=False,
                    add_edge_labels=True, colorscheme=None):

        if colorscheme is None:
            colorscheme = self.DEFAULT_COLOR_SCHEME

        self.reset_lattice()
        self.lattice_nodes = {self.null_node, self.all_node}

        # The order in which the nodes are added is important, i.e. Null --> MUS --> MUAS --> MAS --> MSS
        # Else the output might not be correct
        self.summary_lattice.add_node(self.all_node, **self.get_node_style(self.all_node, colorscheme=colorscheme))
        if 'MUS' in to_highlight:
            self.summary_lattice.add_nodes_from(self.mus_es, **colorscheme['mus_node'])
            self.lattice_nodes.update(self.mus_es)
        if 'MUAS' in to_highlight:
            self.summary_lattice.add_nodes_from(self.muas_es, **colorscheme['muas_node'])
            self.lattice_nodes.update(self.muas_es)
        if 'MAS' in to_highlight:
            self.summary_lattice.add_nodes_from(self.mas_es, **colorscheme['mas_node'])
            self.lattice_nodes.update(self.mas_es)
        if 'MSS' in to_highlight:
            self.summary_lattice.add_nodes_from(self.mss_es, **colorscheme['mss_node'])
            self.lattice_nodes.update(self.mss_es)
        self.summary_lattice.add_node(self.null_node, **colorscheme['sat_node'])  # Must be SAT

        for n in self.lattice_nodes:

            self.summary_lattice.nodes[n]['label'] = self.get_node_label(n, label_format=label_format,
                                                                         display_num_pws=display_num_pws)
            descendants = set(PowersetBitLib.get_descendants(n, self.cmap.num_constraints))
            descendants = descendants.intersection(self.lattice_nodes)
            descendants.remove(n)

            for d in descendants:
                edge_len = self.num_set_bits[d]-self.num_set_bits[n]
                if add_edge_labels:
                    self.summary_lattice.add_edge(n, d, minlen=edge_len, label=str(edge_len),
                                                  **self.get_edge_style((n, d), colorscheme))
                else:
                    self.summary_lattice.add_edge(n, d, minlen=edge_len, **self.get_edge_style((n, d), colorscheme))

        return self.summary_lattice



