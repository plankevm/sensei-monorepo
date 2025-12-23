# Sensei Core Interpreter Specification

This document sketches out the evaluation strategy for sensei core, the
Zig-inspired staged lambda calculus.

## Runtime vs. Compile time separation

- IO is only allowed at runtime
- memory, basic logic, arithmetic is all allowed at both runtime and comptime
- only dynamic types, type introspection is not allowed at runtime

## Comptime evaluation strategy

Inspired by Zig's implementation we follow an "interpret what you can" approach.
This means the input to the interpreter is the runtime program, however the
interpreter will evaluate what it can as it goes along.

If something is not compile time evaluatable like an IO operation we leave that
unevaluated. Other things like arithmetic, function application we evaluate
eagerly. The final output should be an Expression AST node that represents the
runtime program. Comptime evaluated outputs can be via the `Value` variant.

### Evaluation Contexts

When evaluating the interpreter will keep track of a context flag, telling it if
it's in a runtime context or compile time context. It starts in the _runtime
context_.

**Runtime Context**

In a runtime context everything that can be evaluated early is still evaluated
**except for memory allocations**, by default in the runtime context, `malloc`
is considered to create a runtime allocation and is left unevaluated, this will
cause subsequent reads/writes to become runtime as well.

Application of an abstraction who's binding is comptime will trigger the
evaluation of its body in a comptime context (`(lambda comptime x: T. e2) e1`
triggers evaluation of `e2 with x := e1` in comptime context).

In an application if the function to be applied does not have its binding marked
as comptime it is not evaluated. Instead its body is _partially evaluated_. For
comptime abstractions partial evaluation of the body is deferred.

The runtime context is retained unless explicitly changed via a:
- application of a lambda with comptime bind (if the value to be applied is not
  comptime known, error)
- partial evaluation of a body

**Comptime Context**

In the comptime context, similar to Zig's `comptime { ... }` everything must
fully evaluate. In application whether the abstraction's binding is marked
comptime or not it is to be applied in this context. If a function that is not
marked comptime is applied the comptime context is still retained. Bodies of
abstraction who's binding is *not* comptime is partially evaluated. For
unapplied comptime abstractions in a comptime context they are simply retained
as values.

Comptime contexts **cannot** operate on runtime values as they are not known.


**Partial Evaluation Context**

Partial evaluation proceeds similarly to normal evaluation with some subtle
differences, inside abstraction bodies the evaluation of anything with a free
term is deferred similar to how runtime operations are deferred. Bodies of
comptime abstractions are never partially evaluated.

In the partial evaluation context free variables must be kept track of, anything
that's not evaluatable because of free variables is left unevaluated. For
expressions that contain free variables they are to be left unevaluated.

### Memory Model

In a comptime context memory allocations can be made, this is to allow comptime
code to reuse memory primitives & data structures without having to be
rewritten. This memory area is temporary and completely separate from runtime
memory. It only lives for the duration of compile time execution.

This means that it is an error for runtime code to refer to or capture runtime
pointers. However this does not need to be checked in the interpreter, this is
to be deferred to a further checking step.
