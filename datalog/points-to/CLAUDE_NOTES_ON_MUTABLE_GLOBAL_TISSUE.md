# Mutable Global Tissue Analysis

## Overview

The mutable global tissue analysis computes the transitive closure of functions that are "tainted" by mutable or escaped global variables. This identifies which functions may be affected by mutable global state.

## Definition

A function is in the **mutable global tissue** if it:

1. **Directly accesses** a mutable or escaped global variable, OR
2. **Transitively calls** a function that accesses such a global

## Relations

### Input Relations

- `mutated_or_escaped_global(?alloc)` - Global allocations that are either mutated or have escaped
- `global_allocation_by_variable(?var, ?alloc)` - Maps global variables to their allocations
- `operand_points_to(?aCtx, ?alloc, ?ctx, ?operand)` - Points-to analysis results
- `reachable_context(?ctx, ?func)` - Reachable function contexts
- `callgraph_edge(?calleeCtx, ?callee, ?callerCtx, ?callerInstr)` - Call graph edges

### Output Relations

#### `directly_accesses_mutable_global(?func)`
Functions that directly use an operand pointing to a mutable or escaped global allocation.

#### `mutable_global_tissue(?func)`
The complete tissue: all functions that either directly access mutable globals or transitively call such functions.

## Implementation

The analysis uses a simple recursive rule:

```datalog
// Base case: direct access
mutable_global_tissue(?func) :-
    directly_accesses_mutable_global(?func).

// Recursive case: transitive callers
mutable_global_tissue(?caller) :-
    mutable_global_tissue(?callee),
    callgraph_edge(_, ?callee, ?callerCtx, ?callerInstr),
    instr_func(?callerInstr, ?caller).
```

## Usage

The analysis is instantiated for both pointer analysis modes:
- `subset_mutable_global_tissue` - For subset (Andersen-style) analysis
- `unification_mutable_global_tissue` - For unification (Steensgaard-style) analysis

### Output Files

Results are exported to compressed CSV files:
- `subset_mutable_global_tissue.directly_accesses_mutable_global.csv.gz`
- `subset_mutable_global_tissue.mutable_global_tissue.csv.gz`
- `unification_mutable_global_tissue.directly_accesses_mutable_global.csv.gz`
- `unification_mutable_global_tissue.mutable_global_tissue.csv.gz`

## Example

For a program with:
- Global variable `g` that is mutated
- Function `foo()` that accesses `g`
- Function `bar()` that calls `foo()`
- Function `baz()` that calls `bar()`

The tissue would include: `{foo, bar, baz}`

Even though `bar()` and `baz()` don't directly access `g`, they are in the tissue because they transitively call `foo()` which does.

## Security/Analysis Applications

The mutable global tissue is useful for:

1. **Identifying stateful code**: Functions in the tissue depend on mutable global state
2. **Isolation analysis**: Functions NOT in the tissue are potentially pure/isolated from global state
3. **Refactoring guidance**: The tissue boundary indicates where global state dependencies propagate
4. **Security boundaries**: Tissue boundaries may indicate where to place security checks for stateful operations
5. **Testing**: Functions outside the tissue are easier to test in isolation

## Related Analyses

- **Escape Analysis**: Identifies which globals have escaped (input to this analysis)
- **Call Graph**: Provides the transitive caller relationships (input to this analysis)
- **Points-to Analysis**: Determines what allocations each operand may point to (input to this analysis)
