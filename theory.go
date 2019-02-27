// Copyright 2019 Petr Homola. All rights reserved.
// Use of this source code is governed by the AGPL v3.0
// that can be found in the LICENSE file.

package resolution

import (
	//"fmt"
	"strings"
)

type Term interface {
	CtxString(*Context) string
	Unify(*Context, Term, func(*Context))
	Ground(*Context) *Value
}

type Context struct {
	vars   map[*Variable]Term
	server *Server
}

func NewContext() *Context {
	return &Context{make(map[*Variable]Term), NewServer()}
}

func (c *Context) Clone() *Context {
	vars := make(map[*Variable]Term)
	for v, t := range c.vars {
		vars[v] = t
	}
	return &Context{vars, c.server}
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

func (v *Variable) Ground(context *Context) *Value {
	p := v.bottom(context).Pointee(context)
	if v == nil {
		panic("couldn't ground, variable is free")
	}
	return p.(*Value)
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

func (p *Value) InstantiateVariables(vars map[string]*Variable) *Value {
	var args []Term
	for _, arg := range p.Args {
		if v, ok := arg.(*Variable); ok {
			v2 := vars[v.name]
			if v2 == nil {
				v2 = &Variable{v.name}
				vars[v.name] = v2
			}
			args = append(args, v2)
		} else {
			args = append(args, arg.(*Value).InstantiateVariables(vars))
		}
	}
	return &Value{p.Functor, args}
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
		//fmt.Println("?",p1.CtxString(context),"==",p2.CtxString(context))
		if len(p1.Args) == len(p2.Args) && p1.Functor == p2.Functor {
			p1.unify(context, p2, 0, cb)
		}
	}
}

func (v *Value) Ground(context *Context) *Value {
	args := make([]Term, len(v.Args))
	for i, arg := range v.Args {
		args[i] = arg.Ground(context)
	}
	return &Value{v.Functor, args}
}

func (v *Value) Signature() Signature {
	return Signature{v.Functor, len(v.Args)}
}

func (v *Value) TableSignature(context *Context) string {
	s := make([]string, len(v.Args)+1)
	s[0] = v.Functor
	for i, t := range v.Args {
		switch t := t.(type) {
		case *Value:
			s[i+1] = t.CtxString(context)
		case *Variable:
			val := t.bottom(context).Pointee(context)
			if val == nil {
				s[i+1] = "?"
			} else {
				s[i+1] = "@" + val.CtxString(context)
			}
		}
	}
	return strings.Join(s, ":")
}

type Rule struct {
	Head *Value
	Body []*Value
	use  int
}

func NewRule(head *Value, body []*Value) *Rule {
	return &Rule{head, body, 0}
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

func (r *Rule) AddUse() { r.use++ }

func (r *Rule) RelinquishUse() { r.use-- }

func (r *Rule) InstantiateVariables() (*Value, []*Value) {
	if r.use > 0 {
		vars := make(map[string]*Variable)
		head := r.Head.InstantiateVariables(vars)
		var body []*Value
		for _, goal := range r.Body {
			body = append(body, goal.InstantiateVariables(vars))
		}
		return head, body
	} else {
		return r.Head, r.Body
	}
}

type Signature struct {
	Functor string
	Arity   int
}

type Theory struct {
	//Rules []*Rule
	Rules map[Signature][]*Rule
}

func NewTheory(rules []*Rule) *Theory {
	th := &Theory{make(map[Signature][]*Rule)}
	th.AddRules(rules)
	return th
}

func (th *Theory) String() string {
	s := ""
	for _, rules := range th.Rules {
		for _, rule := range rules {
			s += rule.String() + "\n"
		}
	}
	return s
}

type Snapshot struct {
	lengths map[Signature]int
}

func (th *Theory) Snapshot() *Snapshot {
	ss := &Snapshot{make(map[Signature]int)}
	for sig, rules := range th.Rules {
		ss.lengths[sig] = len(rules)
	}
	return ss
}

func (th *Theory) Rollback(ss *Snapshot) {
	for sig, rules := range th.Rules {
		if len, ok := ss.lengths[sig]; ok {
			th.Rules[sig] = rules[:len]
		} else {
			th.Rules[sig] = []*Rule{}
		}
	}
}

func (th *Theory) AddRules(rules []*Rule) {
	for _, rule := range rules {
		th.AddRule(rule)
	}
}

func (th *Theory) AddRule(rule *Rule) {
	sig := rule.Head.Signature()
	list := th.Rules[sig]
	list = append(list, rule)
	th.Rules[sig] = list
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
	//fmt.Println("inferring:",goal.CtxString(context))
	if rules, ok := th.Rules[goal.Signature()]; ok {
		for _, rule := range rules {
			head, body := rule.InstantiateVariables()
			rule.AddUse()
			cont := true
			head.Unify(context, goal, func(context *Context) {
				//fmt.Println("->",goal.CtxString(context))
				cont = th.backchain(context, body, 0, cb)
			})
			rule.RelinquishUse()
			if !cont {
				break
			}
		}
	}
}

type subscriber struct {
	//context  *Context
	callback func(Term)
}

type table struct {
	terms       []*Value
	subscribers []subscriber
}

func (table *table) provide(t Term, context *Context) /*duplicate*/ bool {
	g := t.Ground(context)
	for _, t2 := range table.terms {
		if g.TableSignature(context) == t2.TableSignature(context) {
			return true
		}
	}
	//fmt.Println("tabling:", g.CtxString(context))
	table.terms = append(table.terms, g)
	for _, subscriber := range table.subscribers {
		subscriber.callback(g)
	}
	return false
}

type Server struct {
	tables map[string]*table
}

func NewServer() *Server {
	return &Server{make(map[string]*table)}
}

func (th *Theory) InferTabled(context *Context, goal *Value, cb func(*Context) bool) {
	sig := goal.TableSignature(context)
	if tbl, ok := context.server.tables[sig]; ok {
		//fmt.Println("signature found:", sig)
		for _, t := range tbl.terms {
			goal.Unify(context, t, func(context *Context) {
				cb(context)
			})
		}
		context2 := context.Clone()
		tbl.subscribers = append(tbl.subscribers, subscriber{ /*context,*/ func(t Term) {
			goal.Unify(context2, t, func(context *Context) {
				cb(context)
			})
		}})
	} else {
		//fmt.Println("signature not found:", sig)
		tbl := &table{}
		context.server.tables[sig] = tbl
		if rules, ok := th.Rules[goal.Signature()]; ok {
			for _, rule := range rules {
				head, body := rule.InstantiateVariables()
				rule.AddUse()
				cont := true
				head.Unify(context, goal, func(context *Context) {
					cont = th.backchainTabled(context, body, 0, func(context *Context) bool {
						tbl.provide(goal, context)
						return cb(context)
					})
				})
				rule.RelinquishUse()
				if !cont {
					break
				}
			}
		}
	}
}

func (th *Theory) backchainTabled(context *Context, goals []*Value, i int, cb func(*Context) bool) bool {
	if i == len(goals) {
		return cb(context)
	} else {
		goal := goals[i]
		if goal.Functor == "@cut" && len(goal.Args) == 0 {
			th.backchainTabled(context, goals, i+1, cb)
			return false
		} else {
			cont2 := true
			th.InferTabled(context, goal, func(context *Context) bool {
				cont := th.backchainTabled(context, goals, i+1, cb)
				if !cont {
					cont2 = false
				}
				return cont
			})
			return cont2
		}
	}
}
