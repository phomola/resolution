// Copyright 2019 Petr Homola. All rights reserved.
// Use of this source code is governed by the AGPL v3.0
// that can be found in the LICENSE file.

package resolution

import (
	"fmt"
	"github.com/phomola/resolution/lrparser"
)

type AST interface {
	Description() string
}

type ASTRule struct {
	head ASTTerm
	body []ASTTerm
}

func (a *ASTRule) Description() string {
	s := a.head.Description()
	if len(a.body) > 0 {
		s += " :- "
		for i, t := range a.body {
			if i > 0 {
				s += ", "
			}
			s += t.Description()
		}
	}
	return s + "."
}

func (a *ASTRule) Sem() *Rule {
	vars := make(map[string]*Variable)
	head := a.head.Sem(vars).(*Value)
	var body []*Value
	for _, t := range a.body {
		body = append(body, t.Sem(vars).(*Value))
	}
	return &Rule{head, body, 0}
}

type ASTTerm interface {
	AST
	Sem(vars map[string]*Variable) Term
}

type ASTVar struct {
	name string
}

func (a *ASTVar) Description() string {
	return "$" + a.name
}

func (a *ASTVar) Sem(vars map[string]*Variable) Term {
	v, ok := vars[a.name]
	if !ok {
		v = &Variable{a.name}
		vars[a.name] = v
	}
	return v
}

type ASTValue struct {
	functor string
	args    []ASTTerm
}

func (a *ASTValue) Description() string {
	s := a.functor
	if len(a.args) > 0 {
		s += "("
		for i, arg := range a.args {
			if i > 0 {
				s += ","
			}
			s += arg.Description()
		}
		s += ")"
	}
	return s
}

func (a *ASTValue) Sem(vars map[string]*Variable) Term {
	var args []Term
	for _, t := range a.args {
		args = append(args, t.Sem(vars))
	}
	return &Value{a.functor, args}
}

var grammar = lrparser.NewGrammar([]*lrparser.Rule{
	&lrparser.Rule{"Init", []string{"Stmts"}, func(r []interface{}) interface{} { return r[0] }},
	&lrparser.Rule{"Stmts", []string{"Stmts", "Stmt"}, func(r []interface{}) interface{} { return append(r[0].([]AST), r[1].(AST)) }},
	&lrparser.Rule{"Stmts", []string{"Stmt"}, func(r []interface{}) interface{} { return []AST{r[0].(AST)} }},
	&lrparser.Rule{"Stmt", []string{"Rule"}, func(r []interface{}) interface{} { return r[0] }},
	&lrparser.Rule{"Rule", []string{"Term", "&."}, func(r []interface{}) interface{} { return &ASTRule{head: r[0].(ASTTerm)} }},
	&lrparser.Rule{"Rule", []string{"Term", "&:", "&-", "Terms", "&."}, func(r []interface{}) interface{} { return &ASTRule{r[0].(ASTTerm), r[3].([]ASTTerm)} }},
	&lrparser.Rule{"Term", []string{"_ID"}, func(r []interface{}) interface{} { return &ASTValue{functor: r[0].(*lrparser.Token).Form} }},
	&lrparser.Rule{"Term", []string{"&$", "_ID"}, func(r []interface{}) interface{} { return &ASTVar{r[1].(*lrparser.Token).Form} }},
	&lrparser.Rule{"Term", []string{"&!"}, func(r []interface{}) interface{} { return &ASTValue{functor: "@cut"} }},
	&lrparser.Rule{"Term", []string{"_NUM"}, func(r []interface{}) interface{} { return &ASTValue{functor: r[0].(*lrparser.Token).Form} }},
	&lrparser.Rule{"Term", []string{"_STR"}, func(r []interface{}) interface{} { return &ASTValue{functor: r[0].(*lrparser.Token).Form} }},
	&lrparser.Rule{"Term", []string{"_ID", "&(", "Terms", "&)"}, func(r []interface{}) interface{} {
		return &ASTValue{r[0].(*lrparser.Token).Form, r[2].([]ASTTerm)}
	}},
	&lrparser.Rule{"Terms", []string{"Terms", "&,", "Term"}, func(r []interface{}) interface{} { return append(r[0].([]ASTTerm), r[2].(ASTTerm)) }},
	&lrparser.Rule{"Terms", []string{"Term"}, func(r []interface{}) interface{} { return []ASTTerm{r[0].(ASTTerm)} }},
})

func (th *Theory) AddRulesFromSource(code string) error {
	tokens := lrparser.Tokenize(code, "#")
	ast, err := grammar.Parse(tokens)
	if err == nil {
		var rules []*Rule
		for _, stmt := range ast.([]AST) {
			rule := stmt.(*ASTRule).Sem()
			rules = append(rules, rule)
		}
		th.AddRules(rules)
		return nil
	} else {
		return fmt.Errorf("parse error: %s", err.Error())
	}
}

func NewTheoryFromSource(code string) (*Theory, error) {
	tokens := lrparser.Tokenize(code, "#")
	ast, err := grammar.Parse(tokens)
	if err == nil {
		var rules []*Rule
		for _, stmt := range ast.([]AST) {
			rule := stmt.(*ASTRule).Sem()
			rules = append(rules, rule)
		}
		return NewTheory(rules), nil
	} else {
		return nil, fmt.Errorf("parse error: %s", err.Error())
	}
}
