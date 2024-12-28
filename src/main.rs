//! Symbolic execution is a program analysis method that is used to explore potential execution paths of a program by treating inputs as symbolic representations rather than as concrete values. 
//! Z3 is a satisfiability modulo theory SMT solver that is used to symbolically represent the program, define constraints, and check for satisfiability of those constraints.
//! ## Main Components
//!
//! 1. Script Parsing (`parse_script`):
//!    - Converts raw Bitcoin script into basic blocks
//!    - Handles flow control operations (IF/ELSE/ENDIF)
//!    - Creates structured representation for analysis
//!
//! 2. Control Flow Analysis (`build_edge`):
//!    - Constructs control flow graph from basic blocks
//!    - Handles conditional branches and verification operations
//!    - Manages edge relationships between blocks
//!
//! 3. Symbolic Execution (`sym_exec_block`):
//!    - Performs symbolic execution of script operations
//!    - Maintains stack state and path conditions
//!    - Handles stack operations, cryptographic ops, and conditionals
//!
//! 4. Recursion Detection (`check_recursion`):
//!    - Analyzes execution paths for recursive patterns
//!    - Uses Z3 SMT solver to verify path feasibility
//!    - Identifies script pubkey equality conditions
#[allow(unused)]
use std::collections::{HashMap, HashSet};
use z3::{ast::{Ast, Bool, BV}, Config, Context, Solver};

#[derive(Debug, Clone)]
struct Opcode {
    opcode: String,
    script_pos: u32
}
#[derive(Debug)]
struct Vertex {
    opcodes: Vec<Opcode>,
    id: usize,
    flow_control: Vec<Opcode>,
}

#[derive(Debug)]
struct Edge {
    from_block: usize,
    to_block: usize,
    execute_condition: bool,
}

/// Control flow graph is a collection of basic blocks with edges linking the basic blocks with an associated condition. 
#[derive(Debug, Clone)]
struct ControlFlowGraph<'a> {
    basic_blocks: &'a Vec<Vertex>,
    edges: &'a Vec<Edge>,
}
#[derive(Debug, Clone)]
struct ExecutionPath<'a> {
    stack: Vec<BV<'a>>,
    conditions: Vec<Bool<'a>>,
    block_trace: Vec<usize>,
}
/// Basic block is a sequence of opcodes that are executed sequentially, without encountering any change in the flow of execution
fn parse_script(script: &str) -> Vec<Vertex>{
    let mut basic_blocks: Vec<Vertex> = Vec::new();
    let mut block_opcode: Vec<Opcode> = Vec::new();
    let op_code: Vec<String> = script.split_whitespace().map(|s| s.to_string()).collect();
    let mut block_count: usize = 0;
    for (position, op) in op_code.iter().enumerate() {
        match op.as_str() {
            "OP_IF" | "OP_NOTIF" | "OP_ELSE" | "OP_ENDIF" | "OP_NOP" | "OP_VERIFY" | "OP_RETURN" | "OP_CHECKSEQUENCEVERIFY" |"OP_EQUALVERIFY"|"OP_NUMEQUALVERIFY" | "OP_CHECKSIG"=> {
                if !block_opcode.is_empty() {
                    basic_blocks.push(Vertex {
                        opcodes: block_opcode.clone(),
                        id: block_count,
                        flow_control: vec![Opcode{opcode: op.to_string(),script_pos: position as u32}],
                    });
                }
                else {
                    basic_blocks[block_count-1].flow_control.push(Opcode{opcode: op.to_string(),script_pos: position as u32});
                    // To prevent assigning a block number to empty blocks
                    block_count -=1;
                }
                block_opcode.clear();
                block_count += 1; 
            }
            _ => block_opcode.push(Opcode{opcode: op.to_string(),script_pos: position as u32})
        }
    }
    if !block_opcode.is_empty() {
        basic_blocks.push(Vertex {
            opcodes: block_opcode.clone(),
            id: block_count,
            flow_control: vec![],
        })
    }
    // Adding the terminal block
    basic_blocks.push(Vertex {
        opcodes: vec![Opcode{opcode: "END".to_string(), script_pos: (script.len() +1) as u32}],
        id: block_count,
        flow_control: vec![],
    });
    basic_blocks
}
/// Edge is defined as a connection between two blocks
/// An edge always has a true (or) false condition associated with it
fn build_edge(basic_blocks: &Vec<Vertex>) -> Vec<Edge> {
    let mut edges: Vec<Edge> = Vec::new();
    let mut conditional_stack: Vec<(usize, Option<usize>, Option<usize>, Option<usize>)> = Vec::new();
    for (current_blockid, block) in basic_blocks.iter().enumerate() {
        for flow_op in block.flow_control.iter() {
            match flow_op.opcode.as_str() {
                "OP_IF" | "OP_NOTIF" => {
                    if current_blockid + 1 < basic_blocks.len() {
                        conditional_stack.push((current_blockid, Some(current_blockid + 1), None, None));
                        edges.push(Edge{
                            from_block: block.id,
                            to_block: current_blockid + 1,
                            execute_condition: bool::from(true)
                        });
                    }
                },
                "OP_ELSE" => {
                    if let Some(last) = conditional_stack.last_mut() {
                        if current_blockid +1 < basic_blocks.len() {
                            last.2 = Some(current_blockid + 1);
                        }
                        edges.push(Edge{
                            from_block: last.0, 
                            to_block: current_blockid +1,
                            execute_condition: bool::from(false)
                        });
                    } 
                },
                "OP_ENDIF" => {
                    if let Some((_, if_next, else_next, endif_block)) = conditional_stack.last_mut() {
                        *endif_block = Some(current_blockid);
                        if current_blockid+1 < basic_blocks.len() {
                            edges.push(Edge{
                                from_block: current_blockid,
                                to_block: current_blockid + 1, 
                                execute_condition: bool::from(true)
                            });

                            if let Some(if_next_block) = if_next {
                                if else_next.is_none() {
                                    edges.push(Edge {
                                        from_block: *if_next_block, 
                                        to_block: current_blockid + 1,
                                        execute_condition: bool::from(true)
                                    })
                                }
                            }
                        }
                    }
                    conditional_stack.pop();
                }
                "OP_CHECKSEQUENCEVERIFY" | "OP_EQUALVERIFY" | "OP_NUMEQUALVERIFY" | "OP_CHECKSIG"=> {
                    if current_blockid + 1 < basic_blocks.len() {
                        // Creating an edge for terminal conditons of Verify opcodes
                        edges.push(Edge {
                            from_block: block.id,
                            to_block: basic_blocks.len()-1, // The last block is the terminal block with "END"
                            execute_condition: bool::from(false)
                        });
                        // Creating an edge for successful conditions of verify opcodes
                        if block.flow_control.len() == 1 {
                            edges.push(Edge {
                                from_block: block.id,
                                to_block: current_blockid + 1,
                                execute_condition: bool::from(true)
                            });
                            
                        }
                    }
                },
                _ => {
                    if current_blockid + 1 < basic_blocks.len() {
                        edges.push(Edge {
                            from_block: block.id,
                            to_block: current_blockid + 1,
                            execute_condition: bool::from(true)
                        });
                    }
                }

            }
        }
    }
    edges
}

/// Initialize the stack with the values required for successful execution of the script
fn initialize_stack <'a> (ctx: &Context) -> Vec<BV> {
    let mut stack: Vec<BV> = Vec::new();
    stack.push(BV::fresh_const(ctx, "reclaim_signature", 8*72)); //DER encoded signature with a maximum size of 72 bytes for reclaiming transaction
    stack.push(BV::fresh_const(ctx, "reclaim_pubkey", 8*33)); //compressed publick key for reclaiming transaction
    stack.push(BV::fresh_const(ctx, "conditional_constant", 8)); // To satisfy conditional clause - 0 for IF(outermost), 1 for ELSE(outermost)
    stack.push(BV::fresh_const(ctx, "check_csv_val", 8)); //CSV value
    stack.push(BV::fresh_const(ctx, "pledge_value", 8*8)); // Pledge value
    stack.push(BV::fresh_const(ctx, "funder_hash", 8*20)); //PK hash of the funder
    stack.push(BV::fresh_const(ctx, "funder_pubkey", 8*33)); //PK of the funder
    
    stack
}
/// Symbolocally execute the opcodes in the block and collect the execution results in a struct
/// The stack is modeled as a vector of z3::ast::BV (byte vectors)
fn sym_exec_block<'a>(
    cfg: ControlFlowGraph,
    mut stack: Vec<BV<'a>>,
    ctx: &'a Context,
    current_block: usize,
    visited: &mut HashSet<usize>,
    path_conditions: Vec<Bool<'a>>,
) -> Vec<ExecutionPath<'a>> {
    let blocks = &cfg.basic_blocks[current_block];
    let mut results = Vec::new();
    let current_path = ExecutionPath {
        stack: stack.clone(),
        conditions: path_conditions.clone(), 
        block_trace: vec![current_block],
    };
    for opcode_2d in &blocks.opcodes {
        match opcode_2d.opcode.as_str() {
            "OP_PICK" => {
                let pick_target_bv = stack.pop().unwrap();
                if let Some(num) = pick_target_bv.as_i64() {
                    let picked_value = if let Some(stack_item) = stack.get(stack.len() - 1 - num as usize) {
                        stack_item.clone()
                    } else {
                        continue;
                    };
                    stack.push(picked_value);
                }
            },
            "OP_NUMEQUAL" => {
                if stack.len() > 2 {
                    let first = stack.pop().unwrap();
                    let second = stack.pop().unwrap();
                    let equal_bool = first._eq(&second);
                    let one = BV::from_i64(ctx, 1, 8);
                    let zero = BV::from_i64(ctx, 0, 8);
                    let result = equal_bool.ite(&one, &zero);
                    stack.push(result)
                }
            },
            "OP_ROLL" => {
                let roll_target = stack.pop().unwrap();
                if let Some(num) = roll_target.as_i64() {
                    if num >= 0 && (num as usize) < stack.len() {
                        let roll_value = stack.remove(stack.len() - 1 - num as usize);
                        stack.push(roll_value);
                    }
                }
            },
            "OP_ROT" => {
                if stack.len() >=3 {
                    let stack_len = stack.len();
                    stack.swap(stack_len -1, stack_len -2);
                    stack.swap(stack_len -2, stack_len -3);
                }
            },
            "OP_DROP" => {
                if stack.len() >=1 {
                    stack.pop();
                }
            },
            "OP_2DROP" => {
                if stack.len() >=2 {
                    for _ in 0..2 {
                        stack.pop();
                    }
                }
            },
            "OP_SWAP" => {
                if stack.len() >= 2 {
                    let top = stack.pop().unwrap();
                    let second = stack.pop().unwrap();
                    stack.push(top);
                    stack.push(second);
                }
            },
            "OP_CAT" => {
                if stack.len() >= 2 {
                    let first = stack.pop().unwrap();
                    let second = stack.pop().unwrap();
                    stack.push(first.concat(&second));
                }
            },
            "OP_SHA256" => {
                if stack.len() >=1 {
                    stack.pop();
                    stack.push(BV::new_const(ctx, "sha256_hash", 8*32));
                }
            },
            "OP_HASH160" => {
                if stack.len() >=1 {
                    stack.pop();
                    stack.push(BV::new_const(ctx, "hash160_hash", 8*20));
                }
            },
            "OP_INSPECTOUTPUTSCRIPTPUBKEY" => {
                if stack.len() >=1 {
                    //Assuming that the output script is of p2pkh type
                    stack.pop();
                    // SHA256 hash is always 32 bytes (256 bits)
                    let script_hash = BV::new_const(ctx, "output_script_pubkey", 8 * 32);
                    stack.push(script_hash);
                }
            },
            "OP_INSPECTINPUTSCRIPTPUBKEY" => {
                if stack.len() >=1 {
                    //Assuming that the output script is of p2pkh type
                    stack.pop();
                    // SHA256 hash is always 32 bytes (256 bits)
                    let script_hash = BV::new_const(ctx, "input_script_pubkey", 8 * 32);
                    stack.push(script_hash);
                }
            },
            "OP_PUSHCURRENTINPUTINDEX" => {
                // Push the current input index as a symbolic bitvector
                stack.push(BV::new_const(ctx, "current_input_index", 8*4));
            },
            "OP_INSPECTINPUTVALUE" => {
                if stack.len() >=1 {
                    // Poping the top element, which is the index of the input to inspect
                    stack.pop();
                    stack.push(BV::new_const(ctx, "input_value", 8*8));
                }
            },
            "OP_INSPECTINPUTINDEX" => {
                stack.push(BV::new_const(ctx, "input_index", 8*4));
            }
            "OP_DUP" => {
                if stack.len() >=1 {
                    let top = stack.pop().unwrap();
                    stack.push(top);
                }
            },
            "OP_SUB" => {
                if stack.len() >= 2 {
                    let a = stack.pop().unwrap();
                    let b = stack.pop().unwrap();
                    
                    // Safe size extension
                    let a_size = a.get_size();
                    let b_size = b.get_size();
                    
                    if a_size > 0 && b_size > 0 {
                        let a_ext = if a_size < 256 {
                            a.zero_ext(256 - a_size)
                        } else {
                            a
                        };
                        
                        let b_ext = if b_size < 256 {
                            b.zero_ext(256 - b_size)
                        } else {
                            b
                        };
                        
                        stack.push(b_ext.bvsub(&a_ext));
                    } else {
                        // Handle invalid size case
                        stack.push(BV::new_const(ctx, "invalid_sub_result", 256));
                    }
                }
            },
            "OP_ADD" => {
                if stack.len() >= 2 {
                    let a = stack.pop().unwrap();
                    let b = stack.pop().unwrap();
                    
                    // Safe size extension
                    let a_size = a.get_size();
                    let b_size = b.get_size();
                    
                    if a_size > 0 && b_size > 0 {
                        let a_ext = if a_size < 256 {
                            a.zero_ext(256 - a_size)
                        } else {
                            a
                        };
                        
                        let b_ext = if b_size < 256 {
                            b.zero_ext(256 - b_size)
                        } else {
                            b
                        };
                        
                        stack.push(b_ext.bvadd(&a_ext));
                    } else {
                        // Handle invalid size case
                        stack.push(BV::new_const(ctx, "invalid_add_result", 256));
                    }
                    
                }
            },
            "OP_LESSTHANOREQUAL" => {
                if stack.len() >= 2 {
                    let a = stack.pop().unwrap();
                    let b = stack.pop().unwrap();
                    let result = a.bvsle(&b);
                    stack.push(result.ite(&BV::from_i64(ctx, 1, 1), &BV::from_i64(ctx, 0, 1)));
                }
            },
            "OP_INSPECTOUTPUTVALUE" => {
                if stack.len() >= 1 {
                    stack.pop();
                    stack.push(BV::new_const(ctx, "output_value", 8*8));
                }
            },
            "OP_OVER" => {
                if stack.len() >= 2 {
                    let a = stack[stack.len() - 2].clone();
                    stack.push(a);
                }
            },
            "OP_2OVER" => {
                if stack.len() >= 4 {
                    let a = stack[stack.len() - 4].clone();
                    let b = stack[stack.len() - 3].clone();
                    stack.insert(stack.len() - 1, a);
                    stack.insert(stack.len() - 1, b);
                }
            },
            // Handling hex values
            hex if hex.chars().all(|c| c.is_ascii_hexdigit()) => {
                match hex {
                    // Special case of handling 0xe803 
                    "e803" => {
                        let numeric_value = u64::from_str_radix(hex, 16).unwrap();
                        stack.push(BV::from_u64(ctx, numeric_value, 8*8));
                    }
                    _ => {
                        let hex_value = BV::new_const(ctx, 
                            format!("script_component_{}", hex), 
                            (hex.len() * 4) as u32); // 4 bits per hex char
                        stack.push(hex_value);
                    }
                }
            },
            // Parsing constants in the script
            op if op.starts_with("OP_") => {
                if let Ok(num) = op[3..].parse::<i64>() {
                    if (0..=16).contains(&num) {
                        stack.push(BV::from_i64(ctx, num, 8));
                    }
                }
            },
            _ => {}
        }
    }
    // Handling flow control opcodes
    for flow_op in &blocks.flow_control {
        match flow_op.opcode.as_str() {
            "OP_IF" => {
                if let Some(condition) = stack.last() {
                    let one = BV::from_i64(ctx, 1, 8);
                    let is_true = condition._eq(&one);

                    // Handling symbolic execution for the 'TRUE' condition 
                    if let Some(true_edge) = cfg.edges.iter().find(|e| e.from_block == current_block && e.execute_condition) {
                        let mut true_path = current_path.clone();
                        true_path.conditions.push(is_true.clone());
                        true_path.stack.pop();
                        true_path.block_trace.push(true_edge.to_block);

                        results.extend(sym_exec_block(cfg.clone(), true_path.stack, ctx, true_edge.to_block, &mut visited.clone(), true_path.conditions));
                    }
                    // Handling symbolic executution for the 'FALSE' condition
                    if let Some(false_edge) = cfg.edges.iter().find(|e| e.from_block == current_block && !e.execute_condition) {
                        let mut false_path = current_path.clone();
                        false_path.conditions.push(is_true.not());
                        false_path.stack.pop();
                        false_path.block_trace.push(false_edge.to_block);

                        results.extend(sym_exec_block(cfg.clone(), false_path.stack, ctx, false_edge.to_block, &mut visited.clone(), false_path.conditions));
                    }
                }
            },
            "OP_CHECKSEQUENCEVERIFY" => {
                if let Some(csv_value)=stack.last(){
                    let tx_sequence = BV::new_const(ctx, "tx_sequence", 8);
                    let tx_version = BV::new_const(ctx, "tx_version", 8);
                    //handling symbolic execution for CSV success condition
                    let csv_success = Bool::and(ctx, &[
                        &tx_version.bvuge(&BV::from_i64(ctx, 2, 8)),
                        &csv_value.bvule(&tx_sequence),
                        &csv_value.bvsge(&BV::from_i64(ctx, 0, 8))
                        ]);
                    if let Some(true_edge) = cfg.edges.iter().find(|e| e.from_block == current_block && e.execute_condition) {
                        let mut true_path = current_path.clone();
                        true_path.conditions.push(csv_success.clone());
                        true_path.stack.pop();
                        true_path.block_trace.push(true_edge.to_block);

                        results.extend(sym_exec_block(cfg.clone(), true_path.stack, ctx, true_edge.to_block, &mut visited.clone(), true_path.conditions));
                    }
                    // handling symbolic executution for the 'FALSE' condition
                    if let Some(false_edge) = cfg.edges.iter().find(|e| e.from_block == current_block && !e.execute_condition) {
                        let mut false_path = current_path.clone();
                        false_path.conditions.push(csv_success.not());
                        false_path.stack.pop();
                        false_path.block_trace.push(false_edge.to_block);

                        results.extend(sym_exec_block(cfg.clone(), false_path.stack, ctx, false_edge.to_block, &mut visited.clone(), false_path.conditions));
                    }
                }
            }, 
            "OP_EQUALVERIFY" => {
                if stack.len()>=2{
                    let first = stack.pop().unwrap();
                    let second = stack.pop().unwrap();
                    // Equal verification
                    let equal_bool = first._eq(&second);
                    // Handling equality
                    if let Some(true_edge) = cfg.edges.iter().find(|e| e.from_block == current_block && e.execute_condition) {
                        let mut true_path = current_path.clone();
                        true_path.conditions.push(equal_bool.clone());
                        true_path.stack.pop();
                        true_path.block_trace.push(true_edge.to_block);

                        results.extend(sym_exec_block(cfg.clone(), true_path.stack, ctx, true_edge.to_block, &mut visited.clone(), true_path.conditions));
                    }
                    // handling symbolic executution for the 'FALSE' condition
                    if let Some(false_edge) = cfg.edges.iter().find(|e| e.from_block == current_block && !e.execute_condition) {
                        let mut false_path = current_path.clone();
                        false_path.conditions.push(equal_bool.not());
                        false_path.stack.pop();
                        false_path.block_trace.push(false_edge.to_block);

                        results.extend(sym_exec_block(cfg.clone(), false_path.stack, ctx, false_edge.to_block, &mut visited.clone(), false_path.conditions));
                    }
                }
            }, 
            "OP_CHECKSIG" => {
                if stack.len() >=2 {
                    for _ in 0..2 {
                        stack.pop();
                    }
                    let check_sig = Bool:: fresh_const(ctx, "check_sig");
                    //handling symbolic execution for CHECKSIG success condition
                    if let Some(true_edge) = cfg.edges.iter().find(|e| e.from_block == current_block && e.execute_condition) {
                        let mut true_path = current_path.clone();
                        true_path.conditions.push(check_sig.clone());
                        true_path.stack.pop();
                        true_path.block_trace.push(true_edge.to_block);

                        results.extend(sym_exec_block(cfg.clone(), true_path.stack, ctx, true_edge.to_block, &mut visited.clone(), true_path.conditions));
                    }
                    // handling symbolic executution for the 'FALSE' condition
                    if let Some(false_edge) = cfg.edges.iter().find(|e| e.from_block == current_block && !e.execute_condition) {
                        let mut false_path = current_path.clone();
                        false_path.conditions.push(check_sig.not());
                        false_path.stack.pop();
                        false_path.block_trace.push(false_edge.to_block);

                        results.extend(sym_exec_block(cfg.clone(), false_path.stack, ctx, false_edge.to_block, &mut visited.clone(), false_path.conditions));
                    }
                }
            },
            "OP_NUMEQUALVERIFY" => {
                if stack.len() >= 2 {
                    let second = stack.pop().unwrap();
                    let first = stack.pop().unwrap();
                    if first.get_size() == 32 && second.get_size() == 32 {
                        let equal_bool = first._eq(&second);
                        if equal_bool.as_bool().unwrap_or(false) {
                            // Handling equality
                            if let Some(true_edge) = cfg.edges.iter().find(|e| e.from_block == current_block && e.execute_condition) {
                                let mut true_path = current_path.clone();
                                true_path.conditions.push(equal_bool.clone());
                                true_path.stack.pop();
                                true_path.block_trace.push(true_edge.to_block);
        
                                results.extend(sym_exec_block(cfg.clone(), true_path.stack, ctx, true_edge.to_block, &mut visited.clone(), true_path.conditions));
                            }
                        } else {
                            if let Some(false_edge) = cfg.edges.iter().find(|e| e.from_block == current_block && !e.execute_condition) {
                                let mut false_path = current_path.clone();
                                false_path.conditions.push(equal_bool.not());
                                false_path.stack.pop();
                                false_path.block_trace.push(false_edge.to_block);
        
                                results.extend(sym_exec_block(cfg.clone(), false_path.stack, ctx, false_edge.to_block, &mut visited.clone(), false_path.conditions));
                            }
                        }
                    } else { // If the items poped from the stack are not numbers
                        if let Some(false_edge) = cfg.edges.iter().find(|e| e.from_block == current_block && !e.execute_condition) {
                            let mut false_path = current_path.clone();
                            false_path.conditions.push(Bool::from_bool(ctx, false));
                            false_path.stack.pop();
                            false_path.block_trace.push(false_edge.to_block);
    
                            results.extend(sym_exec_block(cfg.clone(), false_path.stack, ctx, false_edge.to_block, &mut visited.clone(), false_path.conditions));
                        }
                    }
                }
            }
            _ => {}
        }
        // If there are no flow control opcodes associated with a block
        if blocks.flow_control.is_empty() {
            results.push(current_path.clone());
        }
    }
    results
}
/// Analyses execution paths to check for recursion
/// The key condition that is checked for along the various execution paths is if a bitvector representing the input's scriptpubkey is equated with a bitvector representing the output scriptpubkey
/// Solver is the object that checks the satisfiability of the logical conditions. It helps add constraints and check for satisfiability of those constraints. 
fn check_recursion<'a> (paths: Vec<ExecutionPath>, ctx: &'a Context) {
    let solver = Solver::new(ctx);
    for (i, path) in paths.iter().enumerate() {
        println!("Analyzing path {}", i);

        for condition in &path.conditions {
            if condition.to_string().contains("input_script_pubkey") && condition.to_string().contains("output_script_pubkey") {

                solver.push();
                for path_cond in &path.conditions {
                    solver.assert(&path_cond);
                }
                match solver.check() {
                    z3::SatResult::Sat => {
                        println!("Found recurive script in path {}", i);
                        println!("The block trace that lead to recursion {:?}", path.block_trace);
                        println!("The path condition that lead to recursion {:?}", path.conditions);
                    },
                    z3::SatResult::Unsat => {
                        println!("No recursion found in path {}", i);
                    },
                    z3::SatResult::Unknown => {
                        println!("Solver returned unknown for path {}", i);
                    }
                }
                solver.pop(1);
            }
        }
    }
}

fn main() {
    let script = "OP_4 OP_PICK OP_0 OP_NUMEQUAL OP_IF OP_3 OP_ROLL OP_CHECKSEQUENCEVERIFY OP_DROP 76a914 OP_SWAP OP_CAT 88ac OP_CAT OP_SHA256 OP_0 OP_INSPECTOUTPUTSCRIPTPUBKEY OP_EQUALVERIFY e803 OP_PUSHCURRENTINPUTINDEX OP_INSPECTINPUTVALUE OP_DUP OP_4 OP_PICK OP_SUB OP_2 OP_PICK OP_SUB OP_DUP OP_5 OP_PICK OP_4 OP_PICK OP_ADD OP_LESSTHANOREQUAL OP_IF OP_0 OP_INSPECTOUTPUTVALUE OP_2OVER OP_SWAP OP_SUB OP_NUMEQUALVERIFY OP_ELSE OP_0 OP_INSPECTOUTPUTVALUE OP_5 OP_PICK OP_NUMEQUALVERIFY OP_PUSHCURRENTINPUTINDEX OP_INSPECTINPUTSCRIPTPUBKEY OP_1 OP_INSPECTOUTPUTSCRIPTPUBKEY OP_OVER OP_EQUALVERIFY OP_1 OP_INSPECTOUTPUTVALUE OP_2 OP_PICK OP_NUMEQUALVERIFY OP_DROP OP_ENDIF OP_2DROP OP_2DROP OP_2DROP OP_1 OP_ELSE OP_4 OP_ROLL OP_1 OP_NUMEQUALVERIFY OP_4 OP_PICK OP_HASH160 OP_ROT OP_EQUALVERIFY OP_4 OP_ROLL OP_4 OP_ROLL OP_CHECKSIG OP_NIP OP_NIP OP_NIP OP_ENDIF";
    let blocks = parse_script(script);
    println!("Basic Blocks: {:?}", blocks);
    let edges = build_edge(&blocks);
    println!("Edges: {:?}", edges);
    let cfg = ControlFlowGraph { basic_blocks: &blocks, edges: &edges };
    let config = Config::new();
    let ctx = Context::new(&config);
    let initial_stack = initialize_stack(&ctx);
    let initial_block = 0;
    let mut visited = HashSet::new();
    let path_conditions: Vec<Bool> = Vec::new();
    let result_stack = sym_exec_block(cfg, initial_stack, &ctx, initial_block, &mut visited, path_conditions);
    check_recursion(result_stack, &ctx);
}
