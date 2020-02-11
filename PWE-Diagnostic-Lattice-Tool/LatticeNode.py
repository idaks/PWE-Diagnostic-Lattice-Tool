import enum


class NodeEvalState(enum.Enum):
    unevaluated = 0
    evaluated = 1


class NumPWSType(enum.Enum):
    unevaluated = '?'
    exact = 'n'
    atleast = 'n+'


class NodeAmbiguityType(enum.Enum):
    unsat = 0
    unambiguous = 1
    ambiguous = 2


class Node:

    def __init__(self):
        self.eval_state: NodeEvalState = NodeEvalState.unevaluated
        self.num_pws_eval_type: NumPWSType = NumPWSType.unevaluated
        self.num_pws: int = -1
        self.additional_tags: set = set([])

    def update_eval_state(self, eval_state: NodeEvalState):
        self.eval_state = eval_state
        if eval_state == NodeEvalState.unevaluated:
            self.num_pws = -1
            self.num_pws_eval_type = NumPWSType.unevaluated

    def update_num_pws(self, num_pws: int, num_pws_eval_type: NumPWSType=NumPWSType.exact):
        self.num_pws = num_pws
        self.num_pws_eval_type = num_pws_eval_type
        if num_pws_eval_type in [NumPWSType.exact, NumPWSType.atleast]:
            self.update_eval_state(NodeEvalState.evaluated)

    def get_num_pws(self):
        return self.num_pws, self.num_pws_eval_type

    def is_sat(self):
        if (self.eval_state == NodeEvalState.evaluated) and (self.num_pws_eval_type in [NumPWSType.exact, NumPWSType.atleast]):
            return self.num_pws >= 1
        return None

    def is_ambiguous(self):
        if self.eval_state == NodeEvalState.evaluated:
            if self.num_pws_eval_type == NumPWSType.exact:
                if self.num_pws >= 2:
                    return NodeAmbiguityType.ambiguous
                elif self.num_pws == 1:
                    return NodeAmbiguityType.unambiguous
                elif self.num_pws == 0:
                    return NodeAmbiguityType.unsat
            elif self.num_pws_eval_type == NumPWSType.atleast:
                return NodeAmbiguityType.ambiguous if self.num_pws >= 2 else None
        return None
