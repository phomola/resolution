// Copyright 2019 Petr Homola. All rights reserved.
// Use of this source code is governed by the AGPL v3.0
// that can be found in the LICENSE file.

package resolution

import (
//"fmt"
)

type Term interface {
	CtxString(*Context) string
	Unify(*Context, Term, func(*Context))
}

type Context struct {
	vars map[*Variable]Term
}

func NewContext() *Context {
	return &Context{make(map[*Variable]Term)}
}

type Variable struct {
	name string
	//pointee Term
}

func (v *Variable) Pointee(context *Context) Term {
	//return v.pointee
	return context.vars[v]
}

func (v *Variable) SetPointee(context *Context, t Term) {
	//v.pointee = t
	if t != nil {
		context.vars[v] = t
	} else {
		delete(context.vars, v)
	}
}

func (v *Variable) CtxString(context *Context) string {
	b := v.bottom(context)
	if t, ok := b.Pointee(context).(*Value); ok {
		return t.CtxString(context)
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

func (v *Variable) bottom(context *Context) *Variable {
	switch p := v.Pointee(context).(type) {
	case *Variable:
		return p.bottom(context)
	default:
		return v
	}
}

func (v *Variable) Bind(context *Context, t Term) {
	v.bottom(context).SetPointee(context, t)
}

func (v *Variable) Unify(context *Context, t Term, cb func(*Context)) {
	v = v.bottom(context)
	if v.Pointee(context) == nil {
		v.SetPointee(context, t)
		cb(context)
		v.SetPointee(context, nil)
	} else {
		v.Pointee(context).Unify(context, t, cb)
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
				v = &Variable{name}
				vars[name] = v
			}
			terms[i] = v
		} else {
			terms[i] = &Value{arg, nil}
		}
	}
	return &Value{functor, terms}
}

func (p *Value) CtxString(context *Context) string {
	s := p.Functor
	if len(p.Args) > 0 {
		s += "("
		for i, arg := range p.Args {
			if i > 0 {
				s += ","
			}
			s += arg.CtxString(context)
		}
		s += ")"
	}
	return s
}

func (p1 *Value) unify(context *Context, p2 *Value, i int, cb func(*Context)) {
	if i == len(p1.Args) {
		cb(context)
	} else {
		p1.Args[i].Unify(context, p2.Args[i], func(context *Context) {
			p1.unify(context, p2, i+1, cb)
		})
	}
}

func (p1 *Value) Unify(context *Context, p2 Term, cb func(*Context)) {
	if v, ok := p2.(*Variable); ok {
		v.Unify(context, p1, cb)
	} else {
		p2 := p2.(*Value)
		if len(p1.Args) == len(p2.Args) && p1.Functor == p2.Functor {
			p1.unify(context, p2, 0, cb)
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
	s := r.Head.CtxString(nil)
	if len(r.Body) > 0 {
		s += " :- "
		for i, pred := range r.Body {
			if i > 0 {
				s += ", "
			}
			s += pred.CtxString(nil)
		}
	}
	return s + "."
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

func (th *Theory) backchain(context *Context, goals []*Value, i int, cb func(*Context) bool) bool {
	if i == len(goals) {
		return cb(context)
	} else {
		goal := goals[i]
		if goal.Functor == "@cut" && len(goal.Args) == 0 {
			th.backchain(context, goals, i+1, cb)
			return false
		} else {
			cont2 := true
			th.Infer(context, goal, func(context *Context) bool {
				cont := th.backchain(context, goals, i+1, cb)
				if !cont {
					cont2 = false
				}
				return cont
			})
			return cont2
		}
	}
}

func (th *Theory) Infer(context *Context, goal *Value, cb func(*Context) bool) {
	for _, rule := range th.Rules {
		cont := true
		rule.Head.Unify(context, goal, func(context *Context) {
			cont = th.backchain(context, rule.Body, 0, cb)
		})
		if !cont {
			break
		}
	}
}
