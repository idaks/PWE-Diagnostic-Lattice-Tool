from .ConstraintMap import ConstraintMap
from .BitConstraintMap import BitConstraintMap
from .PowersetBitLib import PowersetBitLib
from .LatticeNode import NumPWSType
import networkx as nx


class PowersetFullLatticeViz:

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
        }
    }

    def __init__(self, cmap: BitConstraintMap):
        self.cmap = cmap
        self.full_lattice = self.create_full_lattice(self.cmap.num_constraints)
        self.num_pws = {}
        self.sat_status = {}
        self.resync_lattice()

    def resync_lattice(self):

        self.num_pws = self.cmap.get_all_nodes_num_pws()
        self.sat_status = self.cmap.get_all_nodes_sat()

    def get_node_style(self, node, colorscheme=None):

        if colorscheme is None:
            colorscheme = self.DEFAULT_COLOR_SCHEME

        if self.sat_status[node] is None:
            return colorscheme['unevaluated_node']
        if self.sat_status[node] is True:
            return colorscheme['sat_node']
        if self.sat_status[node] is False:
            return colorscheme['unsat_node']

    def get_edge_style(self, edge, colorscheme=None):

        if colorscheme is None:
            colorscheme = self.DEFAULT_COLOR_SCHEME

        e1, e2 = edge
        if (self.sat_status[e1] is None) or (self.sat_status[e2] is None):
            return colorscheme['unevaluated_edge']
        if self.sat_status[e1] != self.sat_status[e2]:
            return colorscheme['sat_unsat_edge']
        if self.sat_status[e1] is True:
            return colorscheme['sat_sat_edge']
        if self.sat_status[e1] is False:
            return colorscheme['unsat_unsat_edge']

        return colorscheme['unevaluated_edge']

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
            'bitstring': lambda x: PowersetFullLatticeViz.int_to_bit_string(x, self.cmap.num_constraints),
            'int': lambda x: str(x),
            'comp_string': lambda x: "{{{}}}".format(", ".join(self.cmap.int_to_constraint_set(x))),
        }

        label = label_format_to_func[label_format](n) + ('\n({})'.format(num_pws_to_str(*self.num_pws[n]))
                                                         if display_num_pws else '')

        return label

    def color_and_label_lattice(self, display_num_pws=False, label_format='bitstring', to_highlight=('MUS', 'MSS'),
                                colorscheme=None):

        if colorscheme is None:
            colorscheme = self.DEFAULT_COLOR_SCHEME

        for n in self.full_lattice.nodes:
            self.update_node_style(n, self.get_node_style(n, colorscheme))
            self.update_labels({n: self.get_node_label(n, label_format, display_num_pws)})
        for e in self.full_lattice.edges:
            self.update_edge_style(e, self.get_edge_style(e, colorscheme))

        if 'MSS' in to_highlight:
            for n in self.cmap.maximal_satisfiable_constraint_subsets:
                self.update_node_style(n, colorscheme['mss_node'])
        if 'MUS' in to_highlight:
            for n in self.cmap.minimal_unsatisfiable_constraint_subsets:
                self.update_node_style(n, colorscheme['mus_node'])
        if 'MAS' in to_highlight:
            for n in self.cmap.maximal_ambiguous_constraint_subsets:
                self.update_node_style(n, colorscheme['mas_node'])
        if 'MUAS' in to_highlight:
            for n in self.cmap.minimal_unambiguous_constraint_subsets:
                self.update_node_style(n, colorscheme['muas_node'])

    # def _propagate_(self, seed, prop_func, node_style, edge_style, max_level=np.infty):
    #
    #     self.update_node_style(seed, node_style)
    #
    #     if max_level <= 0:
    #         return
    #     next_seeds = prop_func(seed)
    #
    #     for ns in next_seeds:
    #         self.update_edge_style((seed, ns), edge_style)
    #         self._propagate_(ns, prop_func, node_style, edge_style, max_level - 1)

    # def update_with_mus_es_and_mss_es(self, mus_es: set=None, mss_es: set=None, colorscheme=None):
    #
    #     if mus_es is None:
    #         mus_es = self.cmap.minimal_unsatisfiable_constraint_subsets
    #     if mss_es is None:
    #         mss_es = self.cmap.maximal_satisfiable_constraint_subsets
    #     if colorscheme is None:
    #         colorscheme = self.DEFAULT_COLOR_SCHEME
    #
    #     # sat_nodes = set(itertools.chain.from_iterable(
    #     #     PowersetBitLib.get_ancestors(n, 4) for n in mus_es.union(mss_es)
    #     # )).difference(mus_es).difference(mss_es)
    #     #
    #     # unsat_nodes = set(itertools.chain.from_iterable(
    #     #     PowersetBitLib.get_descendants(n, 4) for n in mus_es.union(mss_es)
    #     # )).difference(mss_es).difference(mus_es)
    #     #
    #     # for node in sat_nodes: self.update_node_style(node, colorscheme['sat_node'])
    #     # for node in unsat_nodes: self.update_node_style(node, colorscheme['unsat_node'])
    #
    #     for node in mss_es:
    #         self._propagate_(node, lambda n: PowersetBitLib.get_parents(n, self.cmap.num_constraints),
    #                          colorscheme['sat_node'], colorscheme['sat_sat_edge'])
    #         self._propagate_(node, lambda n: PowersetBitLib.get_children(n, self.cmap.num_constraints),
    #                          colorscheme['unsat_node'], colorscheme['sat_unsat_edge'], max_level=1)
    #         self.update_node_style(node, colorscheme['mss_node'])
    #     for node in mus_es:
    #         self._propagate_(node, lambda n: PowersetBitLib.get_children(n, self.cmap.num_constraints),
    #                          colorscheme['unsat_node'], colorscheme['unsat_unsat_edge'])
    #         self._propagate_(node, lambda n: PowersetBitLib.get_parents(n, self.cmap.num_constraints),
    #                          colorscheme['sat_node'], colorscheme['sat_unsat_edge'], max_level=1)
    #         self.update_node_style(node, colorscheme['mus_node'])

    def update_labels(self, int_to_label_dict: dict):
        for i, label in int_to_label_dict.items():
            self.full_lattice.nodes[i]['label'] = label

    def get_full_lattice(self, display_num_pws=False, label_format='bitstring', to_highlight=('MUS', 'MSS'),
                         colorscheme=None):
        self.color_and_label_lattice(display_num_pws, label_format, to_highlight, colorscheme)
        return self.full_lattice

    @staticmethod
    def _update_node_style_(lattice, node, styles_dict: dict):
        for prop, prop_val in styles_dict.items():
            lattice.nodes[node][prop] = prop_val

    def update_node_style(self, node, styles_dict: dict):
        PowersetFullLatticeViz._update_node_style_(self.full_lattice, node, styles_dict)

    def update_edge_style(self, edge: tuple, styles_dict: dict):
        for prop, prop_val in styles_dict.items():
            self.full_lattice.edges[edge][prop] = prop_val

    @staticmethod
    def int_to_bit_string(num, num_constraints):
        return "".join(['1' if c else '0' for c in PowersetBitLib.int_to_bitlist(num, num_constraints)])

    def reset_lattice(self):
        for n in self.full_lattice.nodes:
            self.update_node_style(n, self.DEFAULT_COLOR_SCHEME['unevaluated_node'])
        for e in self.full_lattice.edges:
            self.update_edge_style(e, self.DEFAULT_COLOR_SCHEME['unevaluated_edge'])

    def create_full_lattice(self, num_constraints, colorscheme=None):

        if colorscheme is None:
            colorscheme = self.DEFAULT_COLOR_SCHEME

        g = nx.Graph()

        g.add_nodes_from(reversed(range(2**num_constraints)))

        for n in range(2**num_constraints):
            g.nodes[n]['label'] = PowersetFullLatticeViz.int_to_bit_string(n, num_constraints)
            PowersetFullLatticeViz._update_node_style_(g, n, colorscheme['unevaluated_node'])
            children = PowersetBitLib.get_children(n, num_constraints)
            g.add_edges_from([(n, c, colorscheme['unevaluated_edge']) for c in children])
            # g.add_edges_from([(n, c) for c in children])

        return g
