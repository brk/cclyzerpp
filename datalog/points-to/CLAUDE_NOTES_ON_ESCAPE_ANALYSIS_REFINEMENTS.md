# Escape Analysis Refinement Opportunities

## Current Implementation

The escape analysis now includes a focused whitelist of known readonly function arguments (see `escape-analysis.dl:75-122`). This handles common cases where mutable global buffers are passed to search/comparison functions like `memchr`, `memcmp`, `bsearch`, and string operations.

## Future Enhancement: LLVM Attribute-Based Refinement

For greater precision without manual whitelisting, the analysis could leverage LLVM's function and parameter attributes. This would require extending the fact generator and schema.

### LLVM Attributes to Extract

#### Function-Level Attributes
- `readonly` / `memory(read)` - Function only reads memory
- `readnone` / `memory(none)` - Function has no memory side effects
- `argmemonly` / `memory(argmem: ...)` - Function only accesses argument memory

#### Parameter-Level Attributes
- `nocapture` - Pointer argument does not escape the function
- `readonly` - Parameter is not written to
- `writeonly` - Parameter is not read from (only written)
- `nonnull` - Parameter cannot be null
- `dereferenceable(N)` - Parameter points to at least N bytes

### Implementation Requirements

#### 1. Fact Generator Changes (`FactGenerator/src/Functions.cpp`)

Add attribute extraction in function processing (~line 90-104):

```cpp
// Extract parameter attributes
for (llvm::Function::const_arg_iterator arg = func.arg_begin(),
                                        arg_end = func.arg_end();
     arg != arg_end; arg++) {
  refmode_t var_id = refmode<llvm::Value>(*arg);
  writeFact(pred::func::param, funcref, index, var_id);
  recordVariable(var_id, arg->getType());

  // NEW: Extract parameter attributes
  if (arg->hasNoCaptureAttr()) {
    writeFact(pred::func::param_attr, funcref, index, "nocapture");
  }
  if (arg->hasAttribute(llvm::Attribute::ReadOnly)) {
    writeFact(pred::func::param_attr, funcref, index, "readonly");
  }
  if (arg->hasAttribute(llvm::Attribute::WriteOnly)) {
    writeFact(pred::func::param_attr, funcref, index, "writeonly");
  }

  index++;
}

// Extract function-level attributes
if (func.onlyReadsMemory()) {
  writeFact(pred::func::attr, funcref, "readonly");
}
if (func.doesNotAccessMemory()) {
  writeFact(pred::func::attr, funcref, "readnone");
}
```

#### 2. Schema Definition (`FactGenerator/include/predicates.inc`)

Add new predicates:

```cpp
GROUP_BEGIN(func)
// ... existing predicates ...
PREDICATE2(func, param_attr)  // func_param_attr(func, index, attr)
PREDICATE2(func, attr)        // func_attr(func, attr)
GROUP_END(func)
```

#### 3. Datalog Schema (`datalog/schema/func.dl`)

Add relation declarations:

```datalog
.decl func_param_attr(func:FunctionDecl, index:ArgumentIndex, attr:symbol)
.decl func_attr(func:FunctionDecl, attr:symbol)
```

#### 4. Escape Analysis Logic (`datalog/points-to/escape-analysis.dl`)

Refine the escaping argument detection:

```datalog
// Don't mark as escaping if parameter has nocapture attribute
escaping_arg(?func, ?index) :-
  func_without_defn(?func),
  func_ty(?func, ?type),
  func_type_param(?type, ?index, ?paramType),
  pointer_type(?paramType),
  !known_readonly_arg(?func, ?index),
  !func_param_attr(?func, ?index, "nocapture").

// Don't mark allocation as escaped if function is readonly
escaped_alloc(?aCtx, ?alloc) :-
  callgraph_edge(_, ?callee, ?callerCtx, ?callerInstr),
  escaping_arg(?callee, ?index),
  actual_arg(?callerInstr, ?index, ?arg),
  operand_points_to(?aCtx, ?alloc, ?callerCtx, ?arg),
  !func_attr(?callee, "readonly"),
  !func_attr(?callee, "readnone").
```

### Benefits

- **Automatic**: No manual whitelist maintenance
- **Precise**: Compiler-verified contracts
- **Complete**: Handles all annotated functions, including custom code
- **Safe**: LLVM guarantees attribute correctness

### Tradeoffs

- **Requires C++ changes**: More invasive than Datalog-only changes
- **Build complexity**: Fact generator must be rebuilt
- **Depends on LLVM annotations**: Old IR or non-optimized code may lack attributes
- **Testing burden**: Requires test cases with various attribute combinations

### Estimated Effort

- Fact generator changes: ~2-4 hours
- Schema updates: ~1 hour
- Datalog refinements: ~2 hours
- Testing: ~4 hours
- **Total: ~1-2 days**

### Compatibility

- Requires LLVM 14+ for modern memory attribute syntax
- Backwards compatible: Missing attributes default to conservative behavior
- Can coexist with whitelist approach (whitelist as fallback)
