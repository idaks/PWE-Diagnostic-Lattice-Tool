from .ConstraintMap import ConstraintMap
from .BitConstraintMap import BitConstraintMap
from .PowersetBitLib import PowersetBitLib
import networkx as nx
import itertools
import numpy as np


class PowersetFullLatticeViz:

    DEFAULT_COLOR_SCHEME = {
        'sat_node': {
            'colorscheme': 'paired9',
            'style': 'filled',
            'color': 3,
            'fillcolor': 3,
        },
        'unsat_node': {
            'colorscheme': 'paired9',
            'style': 'filled',
            'color': 5,
            'fillcolor': 5,
        },
        'mss_node': {
            'colorscheme': 'paired9',
            'style': 'filled',
            'color': 4,
            'fillcolor': 4,
        },
        'mus_node': {
            'colorscheme': 'paired9',
            'style': 'filled',
            'color': 6,
            'fillcolor': 6,
        },
        'unevaluated_node': {
            'colorscheme': 'paired9',
            'style': 'filled',
            'color': 9,
            'fillcolor': 9,
        },
        'sat_sat_edge': {
            'arrowhead': 'none',
            'colorscheme': 'paired9',
            'color': 3,
        },
        'sat_unsat_edge': {
            'arrowhead': 'none',
            'colorscheme': 'paired9',
            'color': 2,
        },
        'unsat_unsat_edge': {
            'arrowhead': 'none',
            'colorscheme': 'paired9',
            'color': 5,
        },
        'unevaluated_edge': {
            'arrowhead': 'none',
            'colorscheme': 'paired9',
            'color': 9,
        }
    }

    def __init__(self, cmap: BitConstraintMap):
        self.cmap = cmap
        self.full_lattice = self.create_full_lattice(self.cmap.num_constraints)

    def _propagate_(self, seed, prop_func, node_style, edge_style, max_level=np.infty):

        self.update_node_style(seed, node_style)

        if max_level <= 0:
            return
        next_seeds = prop_func(seed)

        for ns in next_seeds:
            self.update_edge_style((seed, ns), edge_style)
            self._propagate_(ns, prop_func, node_style, edge_style, max_level - 1)

    def update_full_lattice(self, mus_es: set=None, mss_es: set=None, colorscheme=None):

        if mus_es is None:
            mus_es = self.cmap.minimal_unsatisfiable_constraint_subsets
        if mss_es is None:
            mss_es = self.cmap.maximal_satisfiable_constraint_subsets
        if colorscheme is None:
            colorscheme = self.DEFAULT_COLOR_SCHEME

        # sat_nodes = set(itertools.chain.from_iterable(
        #     PowersetBitLib.get_ancestors(n, 4) for n in mus_es.union(mss_es)
        # )).difference(mus_es).difference(mss_es)
        #
        # unsat_nodes = set(itertools.chain.from_iterable(
        #     PowersetBitLib.get_descendants(n, 4) for n in mus_es.union(mss_es)
        # )).difference(mss_es).difference(mus_es)
        #
        # for node in sat_nodes: self.update_node_style(node, colorscheme['sat_node'])
        # for node in unsat_nodes: self.update_node_style(node, colorscheme['unsat_node'])

        for node in mss_es:
            self._propagate_(node, lambda n: PowersetBitLib.get_parents(n, self.cmap.num_constraints),
                             colorscheme['sat_node'], colorscheme['sat_sat_edge'])
            self._propagate_(node, lambda n: PowersetBitLib.get_children(n, self.cmap.num_constraints),
                             colorscheme['unsat_node'], colorscheme['sat_unsat_edge'], max_level=1)
            self.update_node_style(node, colorscheme['mss_node'])
        for node in mus_es:
            self._propagate_(node, lambda n: PowersetBitLib.get_children(n, self.cmap.num_constraints),
                             colorscheme['unsat_node'], colorscheme['unsat_unsat_edge'])
            self._propagate_(node, lambda n: PowersetBitLib.get_parents(n, self.cmap.num_constraints),
                             colorscheme['sat_node'], colorscheme['sat_unsat_edge'], max_level=1)
            self.update_node_style(node, colorscheme['mus_node'])

    def update_labels(self, int_to_label_dict: dict):
        for i, label in int_to_label_dict.values():
            self.full_lattice.nodes[i]['label'] = label

    def get_full_lattice(self):
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

    def create_full_lattice(self, num_constraints):

        g = nx.Graph()

        g.add_nodes_from(range(2**num_constraints))

        for n in range(2**num_constraints):
            g.nodes[n]['label'] = PowersetFullLatticeViz.int_to_bit_string(n, num_constraints)
            PowersetFullLatticeViz._update_node_style_(g, n, self.DEFAULT_COLOR_SCHEME['unevaluated_node'])
            children = PowersetBitLib.get_children(n, num_constraints)
            g.add_edges_from([(n, c, self.DEFAULT_COLOR_SCHEME['unevaluated_edge']) for c in children])

        return g
