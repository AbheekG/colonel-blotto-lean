# Cost-accounting correspondence

The current library proves functional correctness and bounds for defined
operation traces and work recurrences. Many components compute through explicit
priced primitives and have value-erasure and composition theorems. Some larger
wrappers pair an execution with a separately defined work recurrence.

The remaining verification gap is a complete connection from all implemented
operations to those prices in the paper's abstract real-RAM/bit models. Bounds
on a counter alone do not establish that every required operation was charged.
No concrete omitted charge or incorrect output was identified in the source
audit, but the missing uniform connection prevents claiming complete formal
verification of every implementation-level complexity bound.

The planned strengthening is to specify compositional execution semantics,
connect the existing primitive implementations and recursive programs to it,
and derive the existing cost bounds from that connection. Standard rational
primitive-cost contracts must remain explicit. Any actual undercount exposed
by this work must be repaired without silently weakening the paper's claims.

Compiler correctness, native allocation/reference counting/GC and physical stack
costs are separate from the paper's abstract models and are not targets of this
connection. The existing public theorem contracts remain the baseline while
the stronger correspondence is developed and validated.
