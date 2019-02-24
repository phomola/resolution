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
	if t, ok := b.pointee.(*Value); ok {
		return t.String()
	}
	return "$" + v.name
	/*s := "$" + v.name
	b := v.bottom()
	if t, ok := b.pointee.(StringAtom); ok {
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

type Value struct {
	Functor string
	Args    []Term
}

func NewValue(vars map[string]*Variable, functor string, args ...string) *Value {
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
			terms[i] = &Value{arg, nil}
		}
	}
	return &Value{functor, terms}
}

func (p *Value) String() string {
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

func (p1 *Value) unify(p2 *Value, i int, cb func()) {
	if i == len(p1.Args) {
		cb()
	} else {
		p1.Args[i].Unify(p2.Args[i], func() {
			p1.unify(p2, i+1, cb)
		})
	}
}

func (p1 *Value) Unify(p2 Term, cb func()) {
	if v, ok := p2.(*Variable); ok {
		v.Unify(p1, cb)
	} else {
		p2 := p2.(*Value)
		if len(p1.Args) == len(p2.Args) && p1.Functor == p2.Functor {
			p1.unify(p2, 0, cb)
		}
	}
}

type Rule struct {
	Head *Value
	Body []*Value
}

func NewRule(head *Value, body []*Value) *Rule {
	return &Rule{head, body}
}

func (r *Rule) String() string {
	s := r.Head.String()
	if len(r.Body) > 0 {
		s += " :- "
		for i, pred := range r.Body {
			if i > 0 {
				s += ", "
			}
			s += pred.String()
		}
	}
	return s + "."
}

type Context struct {
}

type Theory struct {
	Rules []*Rule
}

func NewTheory(rules ...*Rule) *Theory {
	return &Theory{rules}
}

func (th *Theory) String() string {
	s := ""
	for _, rule := range th.Rules {
		s += rule.String() + "\n"
	}
	return s
}

func (th *Theory) backchain(goals []*Value, context *Context, i int, cb func() bool) bool {
	if i == len(goals) {
		return cb()
	} else {
		goal := goals[i]
		if goal.Functor == "@cut" && len(goal.Args) == 0 {
			th.backchain(goals, context, i+1, cb)
			return false
		} else {
			cont2 := true
			th.Infer(goal, func() bool {
				cont := th.backchain(goals, context, i+1, cb)
				if !cont {
					cont2 = false
				}
				return cont
			})
			return cont2
		}
	}
}

func (th *Theory) Infer(goal *Value, cb func() bool) {
	context := &Context{}
	for _, rule := range th.Rules {
		cont := true
		rule.Head.Unify(goal, func() {
			cont = th.backchain(rule.Body, context, 0, cb)
		})
		if !cont {
			break
		}
	}
}
