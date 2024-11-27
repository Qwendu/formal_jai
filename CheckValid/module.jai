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
					//compiler_report(tprint("% has success bool", it.expression.name), make_location(it.expression), .INFO);
					continue it;
				}
			}
		}
		for tc.procedure_bodies
		{
			n := 0;
			for :function_calls expr, expr_index : it.expression.block
			{
				header := get_procedure_header_if_compile_time_known(expr);
				if header == null  continue expr;
				if table_find_pointer(*procedures_that_have_success_bool, header.name )
				{
					n += 1;
					n_observed_values := expr.num_return_values_received;
					success_bool_index := index_of_success_bool(header);
					// keep track of the other return values and if they are used
					// if they are used, it needs to be statically proven that success == true
					success_bool_decl : *Code_Declaration;
					variables_to_track : [] *Code_Declaration;
					block : *Code_Block;
					track_variable_use(block, variables_to_track, success_bool_decl);
				}
			}
			N_Functions_Seen += n;
		}
	}
}

Success_State :: enum
{
	// This is the abstract domain
	UNINIT :: 0; // BOT

	TRUE;
	FALSE;

	ANY;  // TOP
}

track_variable_use :: (block : *Code_Block, vars : [] *Code_Declaration, success_bool : *Code_Declaration)
{
	state_before_statements := NewArray(block.statements.count, Success_State);
	for * state_before_statements  it.* = .UNINIT;

	// If use any v in vars while Success_State is UNINIT || FALSE || ANY, error
	
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
	if call.resolved_procedure_expression != null && call.resolved_procedure_expression.kind == .PROCEDURE_HEADER
	{
		return cast(*Code_Procedure_Header)call.resolved_procedure_expression;
	}
	return null;
}

get_procedure_type :: (call : *Code_Procedure_Call) -> *Code_Procedure_Header
{
	id := call.procedure_expression;
	compiler_report(tprint("Procedure does not resolve type is %", type_signature(id.type)), make_location(call), .ERROR);
	return null;
}

_fin :: (p : *Metaprogram_Plugin)
{
	using cast(*CheckValid)p;
	log("Seen % Function Calls that have success : bool", N_Functions_Seen);
}

function_calls :: (block : *Code_Block, code : Code, flags : For_Flags) #expand
{
	// Here I want to also keep track of the Code_Block of the expression
	// Such that I can then iterate over other expressions in the block
	assert(block.block_type == .IMPERATIVE);
	`it : *Code_Procedure_Call;
	`it_index : int;
	stack : [..] *Code_Node;
	array_add(*stack, block);
	while stack.count > 0
	{
		node := pop(*stack);
		if node.kind == .PROCEDURE_CALL
		{
			defer it_index += 1;
			it = cast(*Code_Procedure_Call)node;
			#insert code;
		}
		if node.kind ==
		{
		case .IF; 
			node_if := cast(*Code_If)node;
			if node_if.then_block  array_add(*stack, node_if.then_block);
			if node_if.else_block  array_add(*stack, node_if.else_block);
			if node_if.condition   array_add(*stack, node_if.condition);
		case .WHILE;
			node_while := cast(*Code_While)node;
			array_add(*stack, node_while.condition);
			array_add(*stack, node_while.block);
		case .BLOCK;
			node_block := cast(*Code_Block)node;
			for statement : node_block.statements  array_add(*stack, statement);
		case .BINARY_OPERATOR;
			node_bin := cast(*Code_Binary_Operator)node;
			array_add(*stack, node_bin.left, node_bin.right);
		case .UNARY_OPERATOR;
			node_bin := cast(*Code_Unary_Operator)node;
			array_add(*stack, node_bin.subexpression);
		case .RETURN;
			node_return := cast(*Code_Return)node;
			array_add(*stack, ..node_return.arguments_sorted);
		case .FOR;
			node_for := cast(*Code_For)node;
			array_add(*stack, node_for.iteration_expression);
			array_add(*stack, node_for.block);
		case .CAST;
			node_cast := cast(*Code_Cast)node;
			array_add(*stack, node_cast.expression);
		case .DECLARATION;
			node_declaration := cast(*Code_Declaration)node;
			if node_declaration.expression  array_add(*stack, node_declaration.expression);

		case .USING;
			node_using := cast(*Code_Using)node;
			array_add(*stack, node_using.expression);
		case .MAKE_VARARGS;
			node_make_varargs := cast(*Code_Make_Varargs)node;
			array_add(*stack, ..node_make_varargs.expressions);
		case .DIRECTIVE_CODE;
			node_directive_code := cast(*Code_Directive_Code)node;
			array_add(*stack, node_directive_code.expression);
		case .PROCEDURE_CALL;
			node_procedure_call := cast(*Code_Procedure_Call)node;
			array_add(*stack, ..node_procedure_call.arguments_sorted);
			if node_procedure_call.macro_expansion_block  array_add(*stack, node_procedure_call.macro_expansion_block);
		case .DEFER;
			node_defer := cast(*Code_Defer)node;
			array_add(*stack, node_defer.block);
		case;
			log("[Warning] Unhandled Code_Node.kind == % when iterating over all function call sites", node.kind);
		// We ignore these for now
		case .EXTRACT;
		case .DIRECTIVE_INSERT;
		case .COMPOUND_DECLARATION;
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

		}
	}
}







#import "Compiler";
#import "Basic";
#import "Hash_Table";
