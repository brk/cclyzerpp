# Call Graph Connected Components Analysis

## Overview

This analysis computes connected components in the bipartite call graph, where edges connect call sites to their target functions. The graph is treated as undirected, allowing identification of which call sites and functions are transitively related through calls.

## Key Features

### 1. Bipartite Graph Structure
- **Nodes**: Call sites (CallBase instructions) and callees (Functions or UNKNOWN)
- **Edges**: Represented in `calls_target(site, callee)` relation
- The bipartite structure means edges only exist between call sites and functions, never between two call sites or two functions

### 2. Explicit Unknown Target Tracking
Unknown call targets (indirect calls that cannot be resolved by points-to analysis) are explicitly represented as edges to `"UNKNOWN"`. This allows distinguishing:
- **Fully resolved**: Call site has only known function targets
- **Partially unknown**: Call site has both known targets and unknown targets
- **Fully unknown**: Call site has only unknown target

### 3. Efficient Connected Components with `eqrel`
Uses Soufflé's `eqrel` qualifier which:
- Automatically computes reflexivity, symmetry, and transitivity
- Uses efficient union-find algorithm internally
- Stores only O(n) tuples instead of O(n²) for full transitive closure

## Relations

### Input Relations (from component)
```datalog
callgraph_edge(?calleeCtx, ?callee, ?callerCtx, ?callerInstr)
var_points_to(?aCtx, ?alloc, ?ctx, ?var)
reachable_context(?ctx, ?func)
```

### Base Relations
```datalog
calls_target(site: CallBase, callee: Callee)
```
Bipartite edges from call sites to callees (known functions or UNKNOWN).

```datalog
call_graph_component(x: CGNode, y: CGNode) eqrel
```
Equivalence relation representing connected components. Two nodes are in the same component if they're transitively connected.

### Analysis Relations

#### Component Representatives
```datalog
component_representative(node: CGNode, repr: CGNode)
```
Maps each node to its canonical representative (lexicographically smallest).

#### Component Statistics
```datalog
component_size(repr: CGNode, size: number)
component_call_site_count(repr: CGNode, count: number)
component_callee_count(repr: CGNode, count: number)
component_has_unknown_target(repr: CGNode)
```

#### Call Site Classification
```datalog
call_site_fully_resolved(site: CallBase)
call_site_partially_unknown(site: CallBase)
call_site_fully_unknown(site: CallBase)
```

## Implementation Details

### Unknown Target Detection
A call site gets an edge to `"UNKNOWN"` when:
1. Indirect call/invoke with no points-to information for the function operand
2. Indirect call/invoke where points-to gives a non-function allocation

### Integration
The analysis is implemented as a Soufflé component `ConnectedComponents` that is instantiated for both subset and unification pointer analyses:
- `subset_connected_components`
- `unification_connected_components`

Each instance receives the appropriate callgraph and points-to information from its parent analysis.

## Usage

### Building
The connected components analysis is automatically included when building:
```bash
# For subset analysis
souffle datalog/subset.project

# For unification analysis
souffle datalog/unification.project
```

### Output Files
Results are exported to compressed CSV files:
- `*_connected_components.calls_target.csv`
- `*_connected_components.call_graph_component.csv`
- `*_connected_components.component_representative.csv`
- `*_connected_components.component_size.csv`
- `*_connected_components.component_call_site_count.csv`
- `*_connected_components.component_callee_count.csv`
- `*_connected_components.component_has_unknown_target.csv`
- `*_connected_components.call_site_fully_resolved.csv`
- `*_connected_components.call_site_partially_unknown.csv`
- `*_connected_components.call_site_fully_unknown.csv`

## Example Queries

### Find all nodes in the same component as a function
```datalog
?node :- call_graph_component(?node, "@my_function").
```

### Find the largest components
```datalog
.decl largest_components(repr: CGNode, size: number)
largest_components(?repr, ?size) :-
  component_size(?repr, ?size),
  ?size >= 100.
```

### Count components with unknown targets
```datalog
?count = count : component_has_unknown_target(_).
```

## Comparison to Manual Union-Find

Unlike the unification-based pointer analysis which manually implements union-find with subsumption for performance reasons, this connected components analysis uses the simpler `eqrel` approach because:

1. **No performance constraints**: Connected components is not on the critical path
2. **No choice-domain interaction**: We want all edges, not a single representative per equivalence class
3. **Standard semantics**: We want standard transitive closure, not custom merge behavior
4. **Simplicity**: `eqrel` is declarative and automatically correct

The manual union-find in `points-to/unification.dl` is only necessary for the specific performance requirements of large-scale pointer analysis with carefully orchestrated query plans and subsumption-based updates.
