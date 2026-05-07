"""
Parser for first-order logic formulas.

Supported syntax:
  Negation:     ~  ¬  !
  Conjunction:  /\  ∧
  Disjunction:  \/  ∨
  Implication:  ->  →  (right-associative)
  Universal:    forall x.  ∀x.
  Existential:  exists x.  ∃x.
  Top/Bot:      True  ⊤  /  False  ⊥

Precedence (tightest first): ¬ > ∧ > ∨ > →
Comments start with #.
"""

import re
from ast_nodes import (
    Var, FuncApp, Const,
    Atom, Top, Bot, Neg, And, Or, Implies, Forall, Exists
)


# --- Tokeniser ---

TOKEN_SPEC = [
    ("FORALL",  r"forall\b|∀"),
    ("EXISTS",  r"exists\b|∃"),
    ("TOP",     r"True\b|true\b|⊤"),
    ("BOT",     r"False\b|false\b|_\|_|⊥"),
    ("IMPLIES", r"->|→|=>"),
    ("AND",     r"/\\|∧|&&"),
    ("OR",      r"\\/|∨|\|\|"),
    ("NOT",     r"[~¬!]"),
    ("LPAREN",  r"\("),
    ("RPAREN",  r"\)"),
    ("DOT",     r"\."),
    ("COMMA",   r","),
    ("IDENT",   r"[A-Za-z_][A-Za-z0-9_]*"),
    ("SKIP",    r"\s+|#[^\n]*"),
    ("UNKNOWN", r"."),
]

MASTER_RE = re.compile("|".join(f"(?P<{n}>{p})" for n, p in TOKEN_SPEC))


class LexError(Exception):
    pass

class ParseError(Exception):
    pass


def tokenize(text):
    tokens = []
    for m in MASTER_RE.finditer(text):
        kind = m.lastgroup
        if kind == "SKIP":
            continue
        if kind == "UNKNOWN":
            raise LexError(f"Unexpected character '{m.group()}' at pos {m.start()}")
        tokens.append((kind, m.group(), m.start()))
    tokens.append(("EOF", "", len(text)))
    return tokens


# --- Recursive descent parser ---

class Parser:
    def __init__(self, tokens):
        self.tokens = tokens
        self.pos = 0

    def peek(self):
        return self.tokens[self.pos]

    def consume(self, expected=None):
        kind, val, pos = self.tokens[self.pos]
        if expected and kind != expected:
            raise ParseError(f"Expected {expected} but got {kind} ('{val}') at pos {pos}")
        self.pos += 1
        return kind, val, pos

    def at(self, *kinds):
        return self.tokens[self.pos][0] in kinds

    # formula -> implies
    # implies -> or (-> or)*   right-assoc
    # or      -> and (\/ and)*
    # and     -> unary (/\ unary)*
    # unary   -> ~ unary | forall x. unary | exists x. unary | primary
    # primary -> True | False | ( formula ) | atom
    # atom    -> IDENT ( ( term,... ) )?

    def parse(self):
        return self.implies()

    def implies(self):
        left = self.or_expr()
        if self.at("IMPLIES"):
            self.consume()
            right = self.implies()  # right-assoc
            return Implies(left, right)
        return left

    def or_expr(self):
        left = self.and_expr()
        while self.at("OR"):
            self.consume()
            right = self.and_expr()
            left = Or(left, right)
        return left

    def and_expr(self):
        left = self.unary()
        while self.at("AND"):
            self.consume()
            right = self.unary()
            left = And(left, right)
        return left

    def unary(self):
        if self.at("NOT"):
            self.consume()
            return Neg(self.unary())
        if self.at("FORALL", "EXISTS"):
            return self.quantifier()
        return self.primary()

    def quantifier(self):
        kind, _, _ = self.consume()
        _, var, _ = self.consume("IDENT")
        self.consume("DOT")
        body = self.unary()
        return Forall(var, body) if kind == "FORALL" else Exists(var, body)

    def primary(self):
        kind, val, pos = self.peek()
        if kind == "TOP":
            self.consume()
            return Top()
        if kind == "BOT":
            self.consume()
            return Bot()
        if kind == "LPAREN":
            self.consume()
            f = self.parse()
            self.consume("RPAREN")
            return f
        if kind == "IDENT":
            return self.atom()
        raise ParseError(f"Unexpected token {kind} ('{val}') at pos {pos}")

    def atom(self):
        _, name, _ = self.consume("IDENT")
        args = ()
        if self.at("LPAREN"):
            self.consume()
            if not self.at("RPAREN"):
                args = self.term_list()
            self.consume("RPAREN")
        return Atom(name, args)

    def term_list(self):
        terms = [self.term()]
        while self.at("COMMA"):
            self.consume()
            terms.append(self.term())
        return tuple(terms)

    def term(self):
        _, name, _ = self.consume("IDENT")
        if self.at("LPAREN"):
            self.consume()
            args = () if self.at("RPAREN") else self.term_list()
            self.consume("RPAREN")
            return FuncApp(name, args)
        return Var(name)


# --- Public API ---

def parse(text):
    tokens = tokenize(text)
    p = Parser(tokens)
    formula = p.parse()
    if not p.at("EOF"):
        kind, val, pos = p.peek()
        raise ParseError(f"Unexpected trailing token '{val}' at pos {pos}")
    return formula


def parse_file(path):
    """Parse a file with one formula per line. Returns list of (lineno, formula)."""
    results = []
    with open(path, encoding="utf-8") as f:
        for lineno, line in enumerate(f, 1):
            # strip comments
            if "#" in line:
                line = line[:line.index("#")]
            line = line.strip()
            if not line:
                continue
            try:
                results.append((lineno, parse(line)))
            except (ParseError, LexError) as e:
                raise ParseError(f"Line {lineno}: {e}")
    return results
