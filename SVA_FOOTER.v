/*
RULES:
SVA assertions are written within a property file, but DO NOT rewrite the module interface and DO NOT add includes in the property file (as we already have them in the property file).
DO NOT declare properties; DECLARE assertions named as__<NAME>: assert property (<EXPRESSION>).
DO NOT use [] at the end of assertion NAME. Do not add @(posedge clk) to EXPRESSION.
Assertions must be as high-level as possible, to avoid repeating implementation details.
Above each assertion, write a comment explaining behavior being checked.

$countones(bitarray) returns the number of ONES in bitarray.
&bitarray means that ALL the bits  are ONES.
!(&bitarray) means it's NOT TRUE that ALL the bits are ONES, i.e., SOME of the bits are ZEROS.
|bitarray means that SOME bits is ONES.
!(|bitarray) means that NONE of the bits are ONES, i.e., ALL the bits are ZEROS.


Same-cycle assertions (|->): the precondition and postcondition are evaluated in the same cycle.
Next-cycle assertions (|=>): the precondition is evaluated in the current cycle and the postcondition in the next cycle.
Signals ending in _reg are registers: the assigned value changes in the next cycle.
Signals NOT ending in _reg are wires: the assigned value changes in the same cycle.
The assigned value to wires (signals NOT ending in _reg) can be referenced in the current cycle.
USE a same-cycle assertion (|->) to reason about behavior ocurring in the same cycle.
USE a next-cycle assertion (|=>) to reason about behavior ocurring in the next cycle, for example, the updated value of a _reg.
USE same-cycle assertions (|->) when reasoning about the assigned value of wires (signals NOT ending in _reg).
USE next-cycle assertions (|=>) when reasoning about the data being added to _reg.
DO NOT USE $past() in preconditions, ONLY in postconditions.
DO NOT USE $past() on the postcondition of same-cycle assertion (|->).
On the postcondition of next-cycle assertions (|=>), USE $past() to refer to the value of wires.
On the postcondition of next-cycle assertions (|=>), DO NOT USE $past() to refer to the updated value of _reg.
On the postcondition of next-cycle assertions (|=>), USE $past() to refer to the value of the _reg on the cycle of the precondition, before the register update.
Assertions without precondition DO NOT use |->

Internal signals are those signals NOT present in the module interface. Internal signals are declared within the module.
Referencing internal signals in the property file ALWAYS requires prepending the name of the module before the signal name, e.g., name.<internal_signal>.
NEVER reference internal signals without the module name prefix, e.g., name.<internal_signal>.
DO NOT use foreach loops in assertions; Instead, use generate loops.

TASK:
Write SVA assertions to check correctness of ALL the functionality of the module but the reset behavior.
DO NOT answer anything except for the property file, ONLY write comments within the property file.
*/