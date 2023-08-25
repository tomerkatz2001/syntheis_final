
from adt.tree import Tree
from parsing.earley.earley import Grammar, Parser, ParseTrees
from parsing.silly import SillyLexer



class WhileParser(object):

    TOKENS = r"(\?\?|assert|if|then|else|while|do|skip)(?![\w\d_])   (?P<id>[^\W\d]\w*)   (?P<num>[+\-]?\d+)   (?P<op>[!<>]=|([+\-*/<>=]))    [();]  :=".split()
    GRAMMAR = r"""
    S   ->   S1     |   S1 ; S
    S1  ->   skip   |   id := E   |   if E then S else S1   |   while E do S1
    S1  ->   ( S )
    S1  ->   assert E
    E   ->   E0   |   E0 op E0
    E0  ->   id   |   num  |  ??
    E0  ->   ( E )
    """
    
    def __init__(self):
        self.tokenizer = SillyLexer(self.TOKENS)
        self.grammar = Grammar.from_string(self.GRAMMAR)

    def __call__(self, program_text):
        tokens = list(self.tokenizer(program_text))

        earley = Parser(grammar=self.grammar, sentence=tokens, debug=False)
        earley.parse()
        
        if earley.is_valid_sentence():
            trees = ParseTrees(earley)
            assert(len(trees) == 1)
            return self.postprocess(trees.nodes[0])
        else:
            return None
            
    def postprocess(self, t):
        if t.root in ['γ', 'S', 'S1', 'E', 'E0'] and len(t.subtrees) == 1:
            return self.postprocess(t.subtrees[0])
        elif t.root in ['S', 'S1', 'E'] and len(t.subtrees) == 3 and t.subtrees[1].root in [':=', ';', 'op']:
            return Tree(t.subtrees[1].subtrees[0].root, [self.postprocess(s) for s in [t.subtrees[0], t.subtrees[2]]])
        elif len(t.subtrees) == 3 and t.subtrees[0].root == '(':
            return self.postprocess(t.subtrees[1])
        elif t.root == 'S1' and t.subtrees[0].root in ['if', 'while']:
            return self.postprocess(Tree(t.subtrees[0].root, t.subtrees[1::2]))
        elif t.root == 'S1' and t.subtrees[0].root == 'assert':
            return self.postprocess(Tree(t.subtrees[0].root, [t.subtrees[1]]))
        elif t.root == 'num':
            return Tree(t.root, [Tree(int(t.subtrees[0].root))])  # parse ints

        return Tree(t.root, [self.postprocess(s) for s in t.subtrees])
    
    
    
if __name__ == '__main__':
    ast = WhileParser()("a := 1 ; while a != b do ( i := i + 1 ; if a > b then a := a - b else b := b - a )")
    
    if ast:
        print(">> Valid program.")
        print(ast)
    else:
        print(">> Invalid program.")

