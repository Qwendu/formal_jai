get_plugin :: () -> *Metaprogram_Plugin
{
	p := New(CheckValid);
	return p;
}

CheckValid :: struct
{
	using #as base : Metaprogram_Plugin;
	base.message          = _message;
	base.finish           = _fin;
	procedures_that_have_success_bool : Table(string, *Code_Procedure_Header);
	N_Functions_Seen : int;
}

is_success_bool :: (decl : *Code_Declaration) -> bool
{
	return decl.name == "success" && decl.type_inst && decl.type_inst.result.type == .BOOL;
}

index_of_success_bool :: (header : *Code_Procedure_Header) -> int
{
	for header.returns
	{
		if is_success_bool(it)  return it_index;
	}
	return -1;
}

_message :: (p : *Metaprogram_Plugin, m : *Message)
{
	using cast(*CheckValid)p;

	//log("Message CheckValid");
	if m.kind == .TYPECHECKED
	{
		tc := cast(*Message_Typechecked)m;
		for tc.procedure_headers
		{
			if it.expression.returns.count > 1  for decl : it.expression.returns 
			{
				if is_success_bool(decl)
				{
					table_add(*procedures_that_have_success_bool, it.expression.name, it.expression);
					//compiler_report(tprint("% has success : bool", it.expression.name), make_location(it.expression), .INFO);
					continue it;
				}
			}
		}
		for tc.procedure_bodies  if it.expression.header.name == "main"
		{
			n := 0;
			proc_calls :: #bake_arguments(node_iter(example_node = Code_Procedure_Call.{}));
			for :proc_calls  expr, expr_index : it.expression.block
			{
				header := get_procedure_header_if_compile_time_known(expr);
				if header == null  continue expr;
				if table_find_pointer(*procedures_that_have_success_bool, header.name ) != null
				{
					n += 1;
					//n_observed_values := expr.num_return_values_received;
					//success_bool_index := index_of_success_bool(header);
					//keep track of the other return values and if they are used
					//if they are used, it needs to be statically proven that success == true
					success_bool_decl := stack_element.in_declaration;
					block : *Code_Block = stack_element.surrounding_block;
					abstract_interpret(block, .[success_bool_decl]);
				}
			}
			N_Functions_Seen += n;
		}
	}
}


Bool_Value_Abstract_Domain :: enum
{
	BOT   :: 0x00;
	TRUE  :: 0x01;
	FALSE :: 0x02;
	TOP   :: 0x03;
};

join :: (a : Bool_Value_Abstract_Domain, b : Bool_Value_Abstract_Domain) -> Bool_Value_Abstract_Domain
{
	r := a & b;
	return r;
}

meet :: (a : Bool_Value_Abstract_Domain, b : Bool_Value_Abstract_Domain) -> Bool_Value_Abstract_Domain
{
	r := a | b;
	return r;
}

#if false #run {
	for a : enum_values_as_enum(Bool_Value_Abstract_Domain)
	{
		for b : enum_values_as_enum(Bool_Value_Abstract_Domain)
		{
			log("meet(%1,%2) = %3 join(%1,%2) = %4", a,b, meet(a,b), join(a,b));
		}
	}
}

statement_transform :: (variable_store_before : *Table(*Code_Declaration, Bool_Value_Abstract_Domain), statement : *Code_Node, variable_store_after : type_of(variable_store_before)) -> (changed : bool)
{
	// What effects statement has on the variables in store
	return true;
}


condition_transform :: (variable_store_before : *Table(*Code_Declaration, Bool_Value_Abstract_Domain), condition : *Code_Node, variable_store_after : type_of(variable_store_before)) -> (changed : bool)
{
	return true;
}


abstract_interpret :: (block : *Code_Block, variables_to_track : [] *Code_Declaration)
{
	CFG :: struct
	{
		Edge :: struct
		{// not good for if a == { case ...;} but like for now its okay
			condition : *Code_Node;
			condition_true : *CFG;
			condition_false : *CFG;
		}
		parents : [] *CFG;
		children : Edge;
		statements : [] *Code_Node;
	}

	build_cfg :: (origin : *Code_Block) -> [] *CFG
	{
		all :[..] * CFG;
		blocks_to_visit : [..] struct {
			block : *Code_Block;
			cfg   : *CFG;
		};
		array_add(*blocks_to_visit, .{origin, New(CFG)});
		while blocks_to_visit.count > 0
		{
			using _ := pop(*blocks_to_visit);
			assert(block != null);
			assert(cfg != null);
			start_index := 0;
			//compiler_report("Visiting Block", make_location(block), .INFO);
			for stmt, stmt_index : block.statements
			{
				//compiler_report(tprint("Visiting Statement for cfg %", cfg), make_location(stmt), .INFO);
				if stmt.kind ==
				{
				case .IF;
					node_if := cast(*Code_If)stmt;
					cfg.statements = array_view(block.statements, start_index, stmt_index);
					cfg.children.condition = node_if.condition;
					
					after_if := New(CFG);
					after_if.parents = NewArray(2, *CFG);
					n_used := 0;
					if node_if.then_block
					{
						cfg.children.condition_true = New(CFG);
						cfg.children.condition_true.parents = NewArray(1, *CFG);
						cfg.children.condition_true.parents[0] = cfg;
						array_add(*blocks_to_visit, .{node_if.then_block, cfg.children.condition_true});
						after_if.parents[n_used] = cfg.children.condition_true;
						n_used += 1;
					}
					if node_if.else_block
					{
						cfg.children.condition_false = New(CFG);
						cfg.children.condition_false.parents = NewArray(1, *CFG);
						cfg.children.condition_false.parents[0] = cfg;
						array_add(*blocks_to_visit, .{node_if.else_block, cfg.children.condition_false});
						after_if.parents[n_used] = cfg.children.condition_false;
						n_used += 1;
					}
					after_if.parents.count = n_used;
					start_index = stmt_index + 1;
					array_add(*all, cfg);
					cfg = after_if;
				case;
				}
			}
			cfg.statements = array_view(block.statements, start_index,block.statements.count);
			array_add(*all, cfg);
		}
		return all;
	}
	cfg := build_cfg(block);
	for cfg
	{
		for stmt, stmt_index : it.statements
		{
			compiler_report(tprint("CFG %:%", it, stmt_index), make_location(stmt), .INFO);
		}
	}
}





type_signature :: (t : *Type_Info) -> string
{
	// We are allocating here and never freeing!
	if t.type == 
	{
	case .INTEGER;  return "Integer";
	case .BOOL;     return "Bool";
	case .FLOAT;    return "Float";
	case .PROCEDURE;
		b :String_Builder;
		type_procedure := cast(*Type_Info_Procedure)t;
		append(*b, "(");
		for type_procedure.argument_types  append(*b, type_signature(it));
		append(*b, ") -> (");
		for type_procedure.return_types    append(*b, type_signature(it));
		append(*b, ")");
		return builder_to_string(*b);
	case .STRUCT;  return "Struct";
	case .POINTER; return "Pointer";
	case .TYPE;    return "Type";
	case; return sprint("<unkown Type %>", t.type);
	}
}

get_procedure_header_if_compile_time_known :: (call : *Code_Procedure_Call) -> *Code_Procedure_Header
{
	//compiler_report("uh", make_location(call), .INFO);
	if call.resolved_procedure_expression != null && call.resolved_procedure_expression.kind == .PROCEDURE_HEADER
	{
		return cast(*Code_Procedure_Header)call.resolved_procedure_expression;
	}
	return null;
}

get_procedure_type :: (call : *Code_Procedure_Call) -> *Code_Procedure_Header
{
	id := call.procedure_expression;
	//compiler_report(tprint("Procedure does not resolve type is %", type_signature(id.type)), make_location(call), .ERROR);
	return null;
}

_fin :: (p : *Metaprogram_Plugin)
{
	using cast(*CheckValid)p;
	log("Seen % Function Calls that have success : bool", N_Functions_Seen);
}

node_iter :: (block : *Code_Block, code : Code, flags : For_Flags, $example_node : $T/interface Code_Node) #expand
{
	// Here I want to also keep track of the Code_Block of the expression
	// Such that I can then iterate over other expressions in the block
	assert(block.block_type == .IMPERATIVE);

	Stack_Element :: struct
	{
		node              : *Code_Node;
		surrounding_block : *Code_Block;
		in_declaration    : *Code_Declaration;
	};
	`it : *T;
	`it_index : int;
	`stack_element : Stack_Element;
	stack : [..] Stack_Element;
	array_add(*stack, .{block, block, null});
	while stack.count > 0
	{
		stack_element = pop(*stack);
		node := stack_element.node;
		if node.kind == example_node.kind || type_of(example_node) == Code_Node
		{
			defer it_index += 1;
			it = cast(*type_of(example_node))node;
			#insert code;
		}
		if node.kind ==
		{
		case .IF; 
			node_if := cast(*Code_If)node;
			if node_if.then_block  array_add(*stack, .{node_if.then_block, stack_element.surrounding_block, stack_element.in_declaration});
			if node_if.else_block  array_add(*stack, .{node_if.else_block, stack_element.surrounding_block, stack_element.in_declaration});
			if node_if.condition   array_add(*stack, .{node_if.condition , stack_element.surrounding_block, stack_element.in_declaration});
		case .WHILE;
			node_while := cast(*Code_While)node;
			array_add(*stack, .{node_while.condition, stack_element.surrounding_block, stack_element.in_declaration});
			array_add(*stack, .{node_while.block    , stack_element.surrounding_block, stack_element.in_declaration});
		case .BLOCK;
			node_block := cast(*Code_Block)node;
			for statement : node_block.statements  array_add(*stack, .{statement, node_block, null});
		case .BINARY_OPERATOR;
			node_bin := cast(*Code_Binary_Operator)node;
			array_add(*stack
				, .{node_bin.left , stack_element.surrounding_block, stack_element.in_declaration}
				, .{node_bin.right, stack_element.surrounding_block, stack_element.in_declaration}
			);
		case .UNARY_OPERATOR;
			node_bin := cast(*Code_Unary_Operator)node;
			array_add(*stack, .{node_bin.subexpression, stack_element.surrounding_block, stack_element.in_declaration});
		case .RETURN;
			node_return := cast(*Code_Return)node;
			for node_return.arguments_sorted
			{
				array_add(*stack, .{it, stack_element.surrounding_block, null});
			}
		case .FOR;
			node_for := cast(*Code_For)node;
			array_add(*stack, .{node_for.iteration_expression, stack_element.surrounding_block, stack_element.in_declaration});
			array_add(*stack, .{node_for.block, stack_element.surrounding_block, stack_element.in_declaration});

		case .COMPOUND_DECLARATION;

			node_compound_declaration := cast(*Code_Compound_Declaration)node;
			//for node_compound_declaration.comma_separated_assignment.arguments
			//{
			//	compiler_report(tprint("%", it.node.kind), make_location(it.node), .INFO); // Seem to be IDENT
			//}
			array_add(*stack, .{node_compound_declaration.declaration_properties.expression, stack_element.surrounding_block, node_compound_declaration.declaration_properties});

		case .DECLARATION;
			node_declaration := cast(*Code_Declaration)node;
			if node_declaration.expression  array_add(*stack, .{node_declaration.expression, stack_element.surrounding_block, node_declaration});
		case;
			log("[Warning] Unhandled Code_Node.kind == % when iterating over all function call sites", node.kind);
		// We ignore these for now
		case .DEFER;
		case .PROCEDURE_CALL;
		case .DIRECTIVE_CODE;
		case .MAKE_VARARGS;
		case .CAST;
		case .EXTRACT;
		case .DIRECTIVE_INSERT;

		case .DIRECTIVE_BAKE;
		case .TYPE_DEFINITION;
		case .EXPRESSION_QUERY;
		case .RESOLVED_OVERLOAD; // Maybe this one
		case .TYPE_INSTANTIATION;
		case .DIRECTIVE_RUN;
		case .LITERAL;
		case .IDENT;
		case .CASE;
		case .PROCEDURE_BODY;
		case .TYPE_QUERY;
		case .LOOP_CONTROL;
		case .DIRECTIVE_LOCATION;
		case .DIRECTIVE_COMPILE_TIME;
		case .DIRECTIVE_IMPORT;
		case .CONTEXT;
		case .PROCEDURE_HEADER;
		case .ASM;
		case .STRUCT;
		case .ENUM;
		case .PUSH_CONTEXT;
		case .DIRECTIVE_LIBRARY;
		case .DIRECTIVE_BYTES;
		case .USING;

		}
	}
}



#import "Compiler";
#import "Basic";
#import "Hash_Table";
#import "String";
