// Copyright 2019 Petr Homola. All rights reserved.
// Use of this source code is governed by the AGPL v3.0
// that can be found in the LICENSE file.

package resolution

import (
	"fmt"
)

type Term interface {
	fmt.Stringer
	Unify(Term, func())
}

type Variable struct {
	name    string
	pointee Term
}

func (v *Variable) String() string {
	b := v.bottom()
	if t, ok := b.pointee.(StringConstant); ok {
		return t.text
	}
	return "?[$" + v.name + "]"
	/*s := "$" + v.name
	b := v.bottom()
	if t, ok := b.pointee.(StringConstant); ok {
		s += "{=" + t.text + "}"
	}
	if v != b {
		s += "{=" + b.String() + "}"
	}
	return s*/
}

func (v *Variable) bottom() *Variable {
	switch p := v.pointee.(type) {
	case *Variable:
		return p.bottom()
	default:
		return v
	}
}

func (v *Variable) Bind(t Term) {
	v.bottom().pointee = t
}

func (v *Variable) Unify(t Term, cb func()) {
	v = v.bottom()
	if v.pointee == nil {
		v.pointee = t
		cb()
		v.pointee = nil
	} else {
		v.pointee.Unify(t, cb)
	}
}

type StringConstant struct {
	text string
}

func (s StringConstant) String() string { return s.text }

func (t1 StringConstant) Unify(t2 Term, cb func()) {
	if v, ok := t2.(*Variable); ok {
		v.Unify(t1, cb)
	}
	if t2, ok := t2.(StringConstant); ok {
		if t1.text == t2.text {
			cb()
		}
	}
}

type Predicate struct {
	Functor string
	Args    []Term
}

func NewPredicate(vars map[string]*Variable, functor string, args ...string) *Predicate {
	terms := make([]Term, len(args))
	for i, arg := range args {
		if arg[0] == '$' {
			name := arg[1:]
			v := vars[name]
			if v == nil {
				v = &Variable{name, nil}
				vars[name] = v
			}
			terms[i] = v
		} else {
			terms[i] = StringConstant{arg}
		}
	}
	return &Predicate{functor, terms}
}

func (p *Predicate) String() string {
	s := p.Functor
	if len(p.Args) > 0 {
		s += "("
		for i, arg := range p.Args {
			if i > 0 {
				s += ","
			}
			s += arg.String()
		}
		s += ")"
	}
	return s
}

func (p1 *Predicate) unify(p2 *Predicate, i int, cb func()) {
	if i == len(p1.Args) {
		cb()
	} else {
		p1.Args[i].Unify(p2.Args[i], func() {
			p1.unify(p2, i+1, cb)
		})
	}
}

func (p1 *Predicate) Unify(p2 *Predicate, cb func()) {
	if len(p1.Args) == len(p2.Args) && p1.Functor == p2.Functor {
		p1.unify(p2, 0, cb)
	}
}

type Rule struct {
	Head *Predicate
	Body []*Predicate
}

func NewRule(head *Predicate, body []*Predicate) *Rule {
	return &Rule{head, body}
}

type Theory struct {
	Rules []*Rule
}

func NewTheory(rules ...*Rule) *Theory {
	return &Theory{rules}
}

func (th *Theory) backchain(goals []*Predicate, i int, cb func()) {
	if i == len(goals) {
		cb()
	} else {
		th.Infer(goals[i], func() {
			th.backchain(goals, i+1, cb)
		})
	}
}

func (th *Theory) Infer(goal *Predicate, cb func()) {
	for _, rule := range th.Rules {
		rule.Head.Unify(goal, func() {
			th.backchain(rule.Body, 0, cb)
		})
	}
}
