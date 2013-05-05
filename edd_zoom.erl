-module(edd_zoom).

-export([zoom_graph/1]).


%Pending:
%CUIDAO: EL APPLY ES TRADUEIX A UN CALL. SI EL MODULO NO EXPORTA EIX FUNCIO ES UN ERROR
%poner los cases y sobretodo sus argumentos de manera que al traducir a Core no haya mas de un case en la misma linea 
%las list comprehension en el apply

zoom_graph(Expr)->
	%Clause = 1, %Te que ser un parametro
    {ok,[AExpr|_]} = edd_zoom_lib:parse_expr(Expr++"."),
    FunOperator = erl_syntax:application_operator(AExpr),
    FunArity = length(erl_syntax:application_arguments(AExpr)),
    CoreArgs = [cerl:abstract(erl_syntax:concrete(Arg)) 
                || Arg <- erl_syntax:application_arguments(AExpr)],
	{remote,_,{atom,_,ModName},{atom,_,FunName}} = FunOperator,
	Core = edd_zoom_lib:core_module(atom_to_list(ModName)++".erl"),
	% ONLY TO DEBUG
	compile:file(atom_to_list(ModName)++".erl",[to_core,no_copt]),
	ModuleDefs = cerl:module_defs(Core),
	[Definition|_] = 
	   [Def || {{c_var,[],{FunName_,FunArity_}},Def} <- ModuleDefs, 
	           FunName_ =:= FunName, FunArity_ =:= FunArity],
	CaseFun = cerl:fun_body(Definition),
	InitialCall = cerl:update_c_case(CaseFun, cerl:c_values(CoreArgs), 
	                                 cerl:case_clauses(CaseFun)), 
	%io:format("InitialCall: ~p\n",[InitialCall]), 
    {ok,M} = smerl:for_file(atom_to_list(ModName) ++ ".erl"),
	FunctionDef = 
	    hd([FunctionDef_ || 
              	FunctionDef_ = {function,_,FunName_,Arity_,_} <- smerl:get_forms(M),
		FunName_ =:= FunName, Arity_ =:= FunArity]),
	Env = ets:new(env,[set]),
    ets:insert(Env,{initial_case,true}),
    ets:insert(Env,{function_definition, FunctionDef}),
    ets:insert(Env,{core,Core}),
	{Value,FreeV,Graphs} = get_tree(InitialCall,Env,0), %{c_literal,[],1}
	%io:format("Num. de grafos: ~p\n",[length(Graphs)]),
	%io:format("Roots: ~p\n",[[edd_zoom_lib:look_for_root(G_) || G_ <- Graphs]]),
	G = digraph:new([acyclic]),
	AValue = get_abstract_form(Value),
	% {FunDef,TotalClauses,VarsClause} = 	
	%    get_fundef_and_vars_clause(ModName,FunName,FunArity,Clause),
	TotalClauses = 1,
	RootInfo = {root,{AExpr,AValue}},
	NFreeV = 
	    case TotalClauses of
	         1 -> 
	         	digraph:add_vertex(G,FreeV,RootInfo),
	         	FreeV;
	         _ -> 
		        % digraph:add_vertex(G,FreeV,{function_clause, {FunDef,Clause,VarsClause}}),
		        % digraph:add_vertex(G,FreeV + 1, RootInfo),
		        % digraph:add_edge(G, FreeV + 1, FreeV),
		        FreeV + 1
		end,
	add_graphs_to_graph(G,Graphs),
	[digraph:add_edge(G,NFreeV,edd_zoom_lib:look_for_root(G_)) || G_ <- Graphs],
	edd_zoom_lib:dot_graph_file(G,"dbg_zoom"),
	edd_zoom_lib:ask(G,divide_query),
	%io:format("Env final:\n~p\n",[ets:tab2list(Env)]),
	ets:delete(Env),
	ok.
	
removeDuplicate(List) ->
	gb_sets:to_list(gb_sets:from_list(List)).

check_errors(Value) -> 
    %possiblement falten mes tipos d'errors.
	case Value of
	     {c_literal,[],{error,_}} -> true;
	     _ -> false
	end.

% get_fundef_and_vars_clause(ModName,FunName,Arity,Clause) ->
% 	{ok,M} = smerl:for_file(atom_to_list(ModName) ++ ".erl"),
% 	FunctionDef = 
% 	    hd([FunctionDef_ || 
%               	FunctionDef_ = {function,_,FunName_,Arity_,_} <- smerl:get_forms(M),
% 		FunName_ =:= FunName, Arity_ =:= Arity]),
% 	{function,_,FunName,Arity,Clauses} = FunctionDef,
% 	%io:format("Clauses: ~p\nClause: ~p\n",[length(Clauses),Clause]),
% 	SelectedClause = lists:nth(Clause, Clauses),
% 	Patterns = erl_syntax:clause_patterns(SelectedClause),
% 	{FunctionDef,length(Clauses),
% 	 sets:to_list(sets:union([erl_syntax_lib:variables(Pattern) || Pattern <- Patterns]))}.

get_tree_list([E|Es],Env,FreeV) ->
	{NE,NFreeV,GraphsH} = get_tree(bind_vars(E,Env),Env,FreeV),
	{NEs,NNFreeV,GraphsT} = get_tree_list(Es,Env,NFreeV),
	{[NE|NEs],NNFreeV,GraphsH++GraphsT};
get_tree_list([],_,FreeV) ->
	{[],FreeV,[]}.

build_graphs_and_add_bindings([Var | Vars],Env,FreeV,Value,Deps,GraphsAcc) ->
	VarName = cerl:var_name(Var),
	case atom_to_list(VarName) of
	     [$c,$o,$r | _] -> 
	     	add_bindings_to_env([{Var,Value,Deps,null}],Env),
	     	build_graphs_and_add_bindings(Vars,Env,FreeV,Value,Deps,GraphsAcc); 
	     _ -> 
	     	G = digraph:new([acyclic]),
	     	ConcreteValue = 
	     		case Value of
	     			{anonymous_function,_,_,_,_,_}  ->
	     				get_abstract_form(Value);
	     			_ ->
	     				cerl:concrete(cerl:fold_literal(Value))
	     		end,
			digraph:add_vertex(G,FreeV,{'let',{VarName,ConcreteValue},Deps}),
		    add_bindings_to_env([{Var,Value,Deps,FreeV}],Env),
	        build_graphs_and_add_bindings(Vars,Env,FreeV + 1,Value,Deps,[G | GraphsAcc]) 
	end;
build_graphs_and_add_bindings([],_,FreeV,_,_,GraphsAcc) -> 
	{GraphsAcc,FreeV}.

add_bindings_to_env([{{c_var,_,VarName},Value,Deps,Node}| TailBindings],Env) ->
	ets:insert(Env,{VarName,{Value,Deps,Node}}),
	add_bindings_to_env(TailBindings,Env);
add_bindings_to_env([{VarName,Value,Deps,Node}| TailBindings],Env) ->
	ets:insert(Env,{VarName,{Value,Deps,Node}}),
	add_bindings_to_env(TailBindings,Env);
add_bindings_to_env([],_) -> ok.

get_dependences(Vars, Env) ->
	get_dependences(Vars, Env, []).

get_dependences([Var | Vars], Env, Acc) ->
	VarName = 
		case Var of
			{c_var,_,VarName_} ->
				VarName_;
			_ -> 
				Var
		end,
	%io:format("Variable: ~p\nValues: ~p\n",[VarName,ets:lookup(Env,VarName)]),
	Deps = 
		case ets:lookup(Env,VarName) of 
			[] -> [];
			[{_,{Value,Deps_,Node}}|_] ->
				case atom_to_list(VarName) of 
					[$c,$o,$r | _] -> 
						Deps_;
					_ -> 
						ConcreteValue = 
						case Value of 
							{anonymous_function,_,_,_,_,_} -> 
								get_abstract_form(Value);
							_ -> 
								cerl:concrete(Value)
						end,
						[{VarName,{ConcreteValue,Node}}]
				end
		end,
	get_dependences(Vars, Env, Acc ++ Deps);
get_dependences([], _, Acc) ->
	removeDuplicate(lists:flatten(Acc)).

get_abstract_from_core_literal({c_literal,_,Lit_}) ->
	{ok,[ALit|_]} = edd_zoom_lib:parse_expr(lists:flatten(io_lib:format("~w",[Lit_])++".")),
	ALit.
	
get_abstract_form({anonymous_function,_,_,File,Line,Env}) -> 
	get_fun_from_file(File,Line,Env);
get_abstract_form(Par_) -> 
	Par = cerl:fold_literal(Par_),
	case cerl:is_literal(Par) of
		true -> 
			get_abstract_from_core_literal(Par);
		_ -> 
			{ModName_,FunName_,FunArity_} = get_MFA(Par),
			{'fun',1,
				{function,
				{atom,1,ModName_},
				{atom,1,FunName_},
				{integer,1,FunArity_}}}
	end. 

get_fun_from_file(File,Line,Env) -> 
	AnoFun = 
		case smerl:for_file(File) of
		     {ok,Abstract} ->
			hd(lists:flatten([get_funs_from_abstract(Form,Line) 
			                  || Form <- smerl:get_forms(Abstract)]));
		     {error, {invalid_module, _}} -> 
		     	hd(get(funs_initial_call))
		end,
	PatternsClause = 
		[erl_syntax:clause_patterns(Clause) || Clause <- erl_syntax:fun_expr_clauses(AnoFun)],
	BodyClause = 
		[erl_syntax:clause_body(Clause) || Clause <- erl_syntax:fun_expr_clauses(AnoFun)],
	VariablesPat = 
		sets:union([erl_syntax_lib:variables(Pattern) 
						|| Patterns <- PatternsClause, Pattern <- Patterns]),
	VariablesBody = 
		sets:union([erl_syntax_lib:variables(BodyExpression) 
						|| Body <- BodyClause, BodyExpression <- Body]),
	VarsOnlyInBody = sets:to_list(sets:subtract(VariablesBody, VariablesPat)),
	FunChangeVar =
		fun(T) ->
			case erl_syntax:type(T) of 
				variable -> 
					VarName = erl_syntax:variable_name(T),
					case lists:member(VarName,VarsOnlyInBody) of 
						true ->
							get_abstract_form(bind_vars(cerl:c_var(VarName),Env));
						false ->
							T
					end;
				_ ->
					T
			end
		end,
	erl_syntax:revert(erl_syntax_lib:map(FunChangeVar,AnoFun)).

get_funs_from_abstract(Abstract,Line) -> 
	erl_syntax_lib:fold(fun(Tree,Acc) -> 
	               		case Tree of 
	               	    	     {'fun',Line,{clauses,_}} ->
	               	    		[Tree|Acc];
	               	             {'fun',_,{clauses,_}} when Line =:= -1 ->
	               	    		[Tree|Acc];
	               	    	     _ -> 
	               	    		Acc
	               		end
		    	     end, [], Abstract).

get_MFA(Function) ->
	{c_call,_,{c_literal,_,erlang},{c_literal,_,make_fun},MFA} = Function,
	[{c_literal,_,ModName},{c_literal,_,FunName},{c_literal,_,FunArity}] = MFA,
	{ModName,FunName,FunArity}.

apply_substitution(Expr,Env,Bindings) ->
	cerl_trees:map(
		fun(T)->
			case cerl:type(T) of
			     'var' -> 
			     	case cerl:var_name(T) of
			     	     {_,_} -> T;
			     	     VN ->
			     	     	case ets:lookup(Env,VN) of
			     	     	     [] -> 
			     	     	     	Values = 
			     	     	     	  [Value || {{c_var,_,VarName},Value} <- Bindings,
			     	     	     	            VarName =:= VN],
			     	     	     	case Values of
			     	     	     	     [] -> T;
			     	     	     	     [Value|_] -> 
			     	     	     	     	Value
			     	     	     	end;
			     	     	     [{_,{Value,_,_}}|_] ->
			     	     	     	Value
			     	     	end
			     	end;
			     _ -> T
			end
		end,Expr).

bind_vars(Expr,Env) ->
	%io:format("Expr: ~p\nEnv: ~p\n",[Expr,ets:tab2list(Env)]),
	case Expr of
	     {anonymous_function,_,_,_,_,_} -> Expr;
	     _ ->
			case cerl:type(Expr) of
			     'var' -> 
			     	VarName = cerl:var_name(Expr),
			     	case VarName of
			     	     {FunName,Arity} -> 
			     	     	[_,{file,FileName},_] = cerl:get_ann(Expr),
			     	     	{ModName,_} = lists:split(length(FileName)-4,FileName),
			     	     	MFArgs = 
			     	     	    [{c_literal,[],list_to_atom(ModName)},
	           			     {c_literal,[],FunName},
	          		             {c_literal,[],Arity}],
			     	     	{c_call,[],{c_literal,[],erlang},{c_literal,[],make_fun},MFArgs};
			     	     _ ->
				     		{VarName,{Value,_,_}} = hd(ets:lookup(Env,VarName)),
				     		%io:format("Value: ~p\n",[Value]),
				     		case Value of
			     	             {anonymous_function,_,_,_,_,_} -> Value;
			     	             _ -> cerl:unfold_literal(Value)
			     	        end
			     	end;
			     'values' -> 
			     	Values = cerl:values_es(Expr),
			     	BValues = lists:map(fun(Var) -> bind_vars(Var,Env) end,Values),
			     	{c_values,cerl:get_ann(Expr),BValues};
			    'tuple' -> 
			    	NExps = [bind_vars(E,Env) || E <- cerl:tuple_es(Expr)],
			    	cerl:c_tuple(NExps);
			    'cons' -> 
			    	[NHd,NTl] = [bind_vars(E,Env) || 
			    	             E <- [cerl:cons_hd(Expr),cerl:cons_tl(Expr)]],
			    	cerl:c_cons(NHd,NTl);
			     _ -> Expr
			 end
	 end.

% create_new_env([{c_var,_,VarName}|TailArgs],[Values|TailPars],Env) ->
% 	ets:insert(Env,{VarName,Values}),
% 	create_new_env(TailArgs,TailPars,Env);
% create_new_env([],[],_) -> ok.

get_case_from_abstract(File,Line) -> 
	{ok,Abstract} = smerl:for_file(File),
	lists:flatten(
		[erl_syntax_lib:fold(fun(Tree,Acc) -> 
					%io:format("{Line,Tree}: ~p\n",[{Line,Tree}]),
		               		case Tree of 
		               	    	     {'case',Line,_,_} ->
		               	    		[{Tree,"Case"}|Acc];
		               	             {'if',Line,_} ->
		               	    		[{Tree,"If"}|Acc];
		               	    	     _ -> 
		               	    		Acc
		               		end
			    	     end, [], Form)||Form<-smerl:get_forms(Abstract)]).
	
get_tree_case(Expr,Env,FreeV) -> 
	Args = cerl:case_arg(Expr),
	{ArgsValue,FreeV,[]} = get_tree(Args,Env,FreeV),
	BArgs_ = bind_vars(ArgsValue,Env),
	BArgs = 
		case cerl:type(BArgs_) of
			values -> cerl:values_es(BArgs_);
			_ -> [BArgs_]
		end,
	AbstractCase = 
		case cerl:get_ann(Expr) of 
			[Line,{file,FileName}] ->
				get_case_from_abstract(FileName,Line);
			[] ->
				[]
		end,
	HasAbstractOrIsInitial = 
		(length(AbstractCase) =/= 0) 
		 or 
		  ((length(ets:lookup(Env,initial_case)) =:= 1) 
		  	andalso (hd(ets:lookup(Env,initial_case)) == {initial_case,true})),
	Deps = get_dependences(cerl_trees:variables(Args),Env),
    Clauses = cerl:case_clauses(Expr),
	{ClauseNumber,ClauseBody,Bindings,NFreeV,GraphsClauses} = 
	  get_clause_body(Clauses,Clauses,HasAbstractOrIsInitial,BArgs,Env,FreeV,Deps,1),
	add_bindings_to_env(Bindings,Env),  
	IsInitial = 
		case ets:lookup(Env,initial_case) of 
			[{initial_case,true}|_] ->
				ets:insert(Env,{initial_case,false}),
				true;
			_ ->
				false
		end,
	{Value,NNFreeV,GraphsBody} = get_tree(ClauseBody,Env,NFreeV),
	{NNNFreeV, CaseGraphs} = 
		case AbstractCase of 
			[] -> 
				%io:format("Initial: ~p\n",[ets:lookup(Env,initial_case)]),
				case IsInitial of 
					true ->
						{function_definition,FunctionDef} = 
						 	hd(ets:lookup(Env,function_definition)),
						% 	{function,_,FunName,Arity,Clauses} = FunctionDef,
						Gs =  
							[begin
								G = digraph:new([acyclic]),
								digraph:add_vertex(G,NumNode,
									{fun_clause,{FunctionDef,CaseClause,pattern,SuccFail},[]}),
								digraph:add_edge(G,NNFreeV,NumNode)	,
								case TotalNodes of 
									2 ->
										digraph:add_vertex(G,NumNode + 1,
											{fun_clause,{FunctionDef,CaseClause,guard,SuccFail},[]}),
										digraph:add_edge(G,NumNode, NumNode + 1);
									_ ->
										ok
								end,
								G
							 end || {NumNode,TotalNodes,CaseClause,SuccFail} <- GraphsClauses],
						{NNFreeV, Gs ++ GraphsBody};
					_ -> 
						{NNFreeV, GraphsBody}
				end;
			[_|_] -> 
				G = digraph:new([acyclic]),
				ConcreteBArg = hd([cerl:concrete(BArg) || BArg <- BArgs]),
				digraph:add_vertex(G,NNFreeV,
					{case_if,{hd(AbstractCase),
					 ConcreteBArg,ClauseNumber,
					 cerl:concrete(Value)},Deps}),
				[begin
					digraph:add_vertex(G,NumNode,
						{case_if_clause,{hd(AbstractCase),ConcreteBArg,
						 CaseClause,pattern,SuccFail},Deps}),
					digraph:add_edge(G,NNFreeV,NumNode)	,
					case TotalNodes of 
						2 ->
							digraph:add_vertex(G,NumNode + 1,
								{case_if_clause,{hd(AbstractCase),ConcreteBArg,
								 CaseClause,guard,SuccFail},Deps}),
							digraph:add_edge(G,NumNode, NumNode + 1);
						_ ->
							ok
					end
				 end || {NumNode,TotalNodes,CaseClause,SuccFail} <- GraphsClauses],
				add_graphs_to_graph(G,GraphsBody),
				[digraph:add_edge(G,NNFreeV,edd_zoom_lib:look_for_root(G_)) 
				 	    || G_ <-  GraphsBody],
				{NNFreeV + 1, [G]}
		end,
	%io:format("AbstractCase: ~p\nCaseGraphs: ~p\n",[AbstractCase,CaseGraphs]),
	{Value, NNNFreeV, CaseGraphs}.

get_clause_body([Clause | Clauses],AllClauses,HasAbstractOrIsInitial,BArgs,Env,FreeV,Deps,ClauseNumber) ->
	NClause = cerl:c_clause(cerl:clause_pats(Clause), cerl:clause_body(Clause)),

	FunCreateFailedNode = 
		fun(Type) ->
			{NFreeV, GraphFailed} = 
				case HasAbstractOrIsInitial of
					false ->
				      {FreeV,[]};
				    true ->
				      case Type of 
				      	guard -> 
				      		{FreeV + 2,[{FreeV,2,ClauseNumber,failed}]};
				      	pattern -> 
				      		{FreeV + 1,[{FreeV,1,ClauseNumber,failed}]}
				      end
				  end,
	       	{SelectedClause,NClauseBody,NBindings,NNFreeV,Graphs} =
	       	   get_clause_body(Clauses,AllClauses,HasAbstractOrIsInitial,
	       	                 BArgs,Env,NFreeV,Deps,ClauseNumber + 1),
	       	{SelectedClause,NClauseBody,NBindings,
	       	 NNFreeV,GraphFailed ++ Graphs}
		end,
	%BUArgs = [cerl:unfold_literal(BArg) || BArg <- BArgs],
	%io:format("BArgs: ~p\nNClause: ~p\n",[BArgs,NClause]),
	case cerl_clauses:reduce([NClause| Clauses], BArgs) of
		{true, {{c_clause, _, _, _, ClauseBody}, Bindings}} -> 
			case cerl:clause_body(Clause) of
				ClauseBody -> 
					TempEnv = ets:new(env_guard,[set]),
					ets:insert(TempEnv,ets:tab2list(Env)),
					%{VarsPattern,ValuesPattern} = lists:unzip(Bindings),
					add_bindings_to_env([ {Var, Value, [], null} || {Var,Value} <- Bindings],TempEnv),
					%create_new_env(VarsPattern, [{VP,[],null} , TempEnv),
					{GuardValue,FreeV,[]} = 
						get_tree(cerl:clause_guard(Clause),TempEnv,FreeV),
					ets:delete(TempEnv),
					case cerl:concrete(GuardValue) of
					     true -> 
					     	{NFreeV,GraphGuardSucceeds} = 
					      	   case HasAbstractOrIsInitial of
					      	   		true ->
					      	   			{FreeV + 2,
					      	   			 [{FreeV,2,ClauseNumber,succeed}]};
					      	        false ->
					      	          	{FreeV,[]}
					      	   end,
					      	Node = 
					      		case NFreeV of
					      			FreeV ->
					      				null;
					      			_ -> 
					      				FreeV
					      		end,
					      	%io:format("Bindings: ~p\nNode: ~p\n", [Bindings,Node]),
					      	NBindings =
					      	 [{BinVar, BinValue, Deps, Node} || {BinVar, BinValue} <- Bindings],
					     	{ClauseNumber,ClauseBody,NBindings,NFreeV,GraphGuardSucceeds};
					     false ->
					      	FunCreateFailedNode(guard)
					end;
				_ -> 
				 	FunCreateFailedNode(pattern)
			end;
		_ -> 
			FunCreateFailedNode(pattern)
	end;
get_clause_body([],_,_,_,_,_,_,_) -> 
	throw({error,"Non matching clause exists"}).

add_graphs_to_graph(G,Graphs) ->
	[begin 
	  {V,Label} = digraph:vertex(G_,V),
%	  {StrLabel,_} = Label,
%	  NLabel = {StrLabel++ ", with: "++ Context,0},
	  digraph:add_vertex(G,V,Label) 
	 end || G_ <- Graphs,V <- digraph:vertices(G_)],
	[digraph:add_edge(G,V1,V2) || G_ <- Graphs,V1 <- digraph:vertices(G_),
	                              V2 <- digraph:out_neighbours(G_, V1)].
	

get_tree_call(Call,Env0,FreeV) -> 
	ModName = cerl:concrete(bind_vars(cerl:call_module(Call),Env0)),
	FunName = cerl:concrete(bind_vars(cerl:call_name(Call),Env0)),
	Args = cerl:call_args(Call),
	%Quitar funciones de esta lista
	%io:format("Args: ~p\n",[[cerl:call_module(Call),cerl:call_name(Call)|Args]]),
	%io:format("GraphVars: ~p\n",[GraphVars]),
%	io:format("FUNCTION CALL ~p:~p/~p\n",[ModName,FunName,FunArity]),
    BArgs = lists:map(fun(Arg) -> bind_vars(Arg,Env0) end,Args),
    %io:format("BArgs: ~p\n",[BArgs]),
 	NoLits = 
     	case [BArg || BArg = {anonymous_function,_,_,_,_,_} <- BArgs] of
     	     [] ->
     	        [BArg || BArg <- BArgs,
     	                 not cerl:is_literal(cerl:fold_literal(BArg))];
     	     List -> List
     	end,
     	%io:format("NoLits: ~p\n",[NoLits]),
 	case NoLits of
 	     [] -> 
 	     	ABArgs = [get_abstract_from_core_literal(cerl: fold_literal(BArg)) || BArg <- BArgs],
 	     	%io:format("ABArgs: ~p\n",[ABArgs]),
 	     	Value =  
				try
		      	% Posible problema si el ya existe un módulo foo
				   M1 = smerl:new(foo),
				   {ok, M2} = 
				      smerl:add_func(M1, 
				          {function,1,bar,0,
			                    [{clause,1,[],[],
			                     [{call,1,{remote,1,{atom,1,ModName},
				                               {atom,1,FunName}},ABArgs}]}]}),
		            smerl:compile(M2,[nowarn_format]),
		            foo:bar() %Genera el valor utilizando el módulo creado
		                      %on de fly
				catch
				   Exception:Reason -> {Exception,Reason}
				end,
			CValue = cerl:abstract(Value),
			%io:format("AValue: ~p\n\n",[AValue]),
			{CValue,FreeV,[]};
	     _ -> 
	        case {ModName,FunName} of
	             {'erlang','is_function'} ->
	                case BArgs of
	                     [Function = {c_call,_,{c_literal,_,erlang},
	                      {c_literal,_,make_fun},_} | MayBeArity] ->
	                       {_,_,CFunArity} = get_MFA(Function),
	                       case lists:map(fun cerl:concrete/1,MayBeArity) of
     	                            [] ->  {{c_literal,[],true},FreeV,[]};
     	                            [CFunArity] -> {{c_literal,[],true},FreeV,[]};
     	                            _ -> {{c_literal,[],false},FreeV,[]}
     	                    end;
	                     [{anonymous_function,_,AFunCore,_,_,_} | MayBeArity] ->
    	                       AFunArity = cerl:fun_arity(AFunCore),
    	                       case lists:map(fun cerl:concrete/1,MayBeArity) of
    	                            [] ->  {{c_literal,[],true},FreeV,[]};
    	                            [AFunArity] -> {{c_literal,[],true},FreeV,[]};
    	                            _ -> {{c_literal,[],false},FreeV,[]}
    	                       end; 
	                     _ ->
	                       {{c_literal,[],false},FreeV,[]}
	                end;
	             _ ->
	               	FileAdress = code:where_is_file(atom_to_list(ModName)++".erl"),
					% Busca el erl. Si no está, busca el beam (libreria de sistema) y tunea la ruta
					% para apuntar al ebin/ correspondiente
					NFileAdress = 
					   case FileAdress of
					        non_existing -> 
					     		NFileAdress_ = 
					     		   code:where_is_file(atom_to_list(ModName)++".beam"),
					     		case NFileAdress_ of
					     		     non_existing -> 
					     		     	throw({error,"Non existing module",ModName});
					     		     _ -> 
					     		     	RelPath = "ebin/" ++ 
					     		     	           atom_to_list(ModName) ++ ".beam",
					     		     	NRelPath = "src/" ++ 
					     		     	           atom_to_list(ModName) ++ ".erl",
					     		     	PrevPath = 
					     		     	  lists:sublist(NFileAdress_,
					     		     	     1,length(NFileAdress_)-length(RelPath)),
					     		     	PrevPath ++ NRelPath
					     		end;
					     	_ -> FileAdress
					   end,
	               ModCore = edd_zoom_lib:core_module(NFileAdress),
	               EnvApply = ets:new(FunName, [set]),
	               ets:insert(EnvApply, {core,ModCore}),
	               FunArity = cerl:call_arity(Call),
	               get_tree_apply(cerl:ann_c_apply(cerl:get_ann(Call),
	                            cerl:c_var({FunName,FunArity}),Args),
	                     EnvApply,FreeV)
	        end
	        
	 end.


extract_module_from_ann([_,{file,File}]) ->
	[_,_,_,_|ModName_] = lists:reverse(File),
	list_to_atom(lists:reverse(ModName_)).

get_tree_apply(Apply,Env0,FreeV)->
	FunVar = cerl:apply_op(Apply),
	%io:format("Apply: ~p\nFunVar: ~p\nModule: ~p\nEnv0: ~p\nTrusted: ~p\n",[Apply,FunVar,cerl:module_name(Core),ets:tab2list(Env0),Trusted]),
	Pars = cerl:apply_args(Apply),
	NPars = lists:map(fun(Par) -> bind_vars(Par,Env0) end,Pars),
	{core,Core} = hd(ets:lookup(Env0,core)),
	FunDefs = cerl:module_defs(Core),
	case FunVar of 
		{anonymous_function,_,{c_fun,_,Args,FunBody},_,_,_} ->
			get_tree_apply_fun(Args,NPars,FreeV,FunBody,[]);
		_ -> 
			case cerl:type(FunVar) of
				'var' ->
					case cerl:var_name(FunVar) of
					     {FunName,_} ->
							case [FunBody_ || {{c_var,_,FunName_},FunBody_} <- FunDefs, 
							                  FunName_ == cerl:var_name(FunVar)] of
							     [{c_fun,_,Args,FunBody}|_] -> % apply 'd'/1 (3)
							     	get_tree_apply_fun(Args,NPars,FreeV,FunBody,[]);
							     _ -> % Apply de ¿?
							     	get_tree_call(
							     	  cerl:ann_c_call(cerl:get_ann(Apply),
							     	              {c_literal,[],extract_module_from_ann(cerl:get_ann(Apply))},
							     	              {c_literal,[],FunName},Pars),Env0,FreeV)
							end;
					     _ -> % Apply de una variable
					     	BFunVar = bind_vars(FunVar,Env0),
					     	case BFunVar of
					     	     {anonymous_function,_,{c_fun,_,Args,FunBody},_,_,_} -> % Se enlaza a una función anónima
					     	        % {anonymous,{c_fun,_,Args,FunBody},_,_,_} = 
					     	        %         get_anon_func(EnvAF,FunName,FunCore),
						           get_tree_apply_fun(Args,NPars,FreeV,FunBody,[]);
					     	     _ -> % Caso de un make_fun
							     	{ModName,FunName,_} = get_MFA(BFunVar),
							     	get_tree_call({c_call,cerl:get_ann(Apply),
							     	            	{c_literal,[],ModName},{c_literal,[],FunName},NPars},
						     	            		ets:new(env, [set]),FreeV)
							end
					end;
				_ -> 
					{ModName,FunName,_} = get_MFA(FunVar),
			     	get_tree_call({c_call,cerl:get_ann(Apply),
			     	            {c_literal,[],ModName},{c_literal,[],FunName},NPars},
			     	             ets:new(env, [set]),FreeV)
			end
		end.
	
get_tree_apply_fun(Args,NPars,FreeV,FunBody,Env0) ->
	Env = ets:new(env_temp, [set]),
	add_bindings_to_env([ {Var, Value, [], null} || {Var,Value} <- lists:zip(Args,NPars)],Env),
	%create_new_env(Args, NPars, Env),
	%io:format("Env0: ~p\nEnv: ~p\n",[Env0,ets:tab2list(Env]),
	add_bindings_to_env(Env0,Env),
	Value = get_tree(FunBody,Env,FreeV),
	ets:delete(Env),
	Value.
	% IsLC = % Detecta si se trata de una list comprehension
	% 	case FunVar of 
	% 	  {anonymous_function,_,_,_,_,_} ->
	% 	  	false;
	% 	  _ ->
	% 		  case cerl:var_name(FunVar) of
	% 		       {FunName,_} ->
	% 		     	  SFunName = atom_to_list(FunName), 
	% 				  case SFunName of
	% 					[$l,$c,$$,$^|_] -> true;
	% 					_ -> false
	% 				  end;
	% 			       _ -> false
	% 		  end
	% 	end,
	% [AValue|APars] = 
	%   lists:map(fun get_abstract_form/1,[Value|NPars]),
	% AApply =  
	%   case FunVar of 
	%      {anonymous_function,_,_,_,_,_} ->
	%      	{call,1,get_abstract_form(FunVar),APars};
	%      _ ->
	% 	  case  cerl:var_name(FunVar) of
	% 		{FunName,_} ->
	% 			case IsLC of
	% 			     true ->
	% 			     	"";
	% 			     _ -> 
	% 			     	case Trusted of
	% 			     	     true -> "";
	% 			     	     _ -> 
	% 					{call,1,{remote,1,
	% 					          {atom,1,cerl:concrete(cerl:module_name(Core))},
	% 					          {atom,1,FunName}},APars}
	% 				end
	% 			end;
	% 		_ -> 
	% 			{call,1,get_abstract_form(FunName),APars}
	% 	  end
	%    end,
	% case AApply of 
	%      "" -> 
	%      	{Value,NFreeV,Roots};
	%      _ -> 
	% 		digraph:add_vertex(G,NFreeV,
	% 		                   {erl_prettypr:format({match,1,AApply,AValue},
	% 		                                       [{paper, 300},{ribbon, 300}]),
	% 		                    get(CaseId)}),
	% 		[digraph:add_edge(G,NFreeV,Root) || Root <- Roots],
	% 		{Value,NFreeV+1,[NFreeV]}
	% end.



% get_tree_apply(Apply,Env0,FreeV)->
% 	FunVar = cerl:apply_op(Apply),
% 	%io:format("Apply: ~p\nFunVar: ~p\nModule: ~p\nEnv0: ~p\nTrusted: ~p\n",[Apply,FunVar,cerl:module_name(Core),ets:tab2list(Env0),Trusted]),
% 	%io:format("Apply: ~p\nTrusted: ~p\n",[Apply,Trusted]),
% 	Pars = cerl:apply_args(Apply),
% 	%NPars = lists:map(fun(Par) -> bind_vars(Par,Env0) end,Pars),
% 	%FunDefs = cerl:module_defs(Core),
% 	case cerl:var_name(FunVar) of
% 	     {FunName,_} ->
% 	     	get_tree_call(
% 	     	  cerl:ann_c_call(cerl:get_ann(Apply),
% 	     	              {c_literal,[],extract_module_from_ann(cerl:get_ann(Apply))},
% 	     	              {c_literal,[],FunName},Pars),Env0,FreeV);
% 	     _ -> % Apply de una variable
% 	     	ok
% 	     	% BFunVar = bind_vars(FunVar,Env0),
% 	     	% GraphsVar = get_graphs_var(FunVar,Env0),
% 	     	% case BFunVar of
% 	     	%      {anonymous_function,FunName,FunCore,File,Line,GrahpsFA} -> % Se enlaza a una función anónima
% 	     	%         {c_fun,_,Args,FunBody} = FunCore,
% 	      %           getTreeApplyFun(Args,NPars,FreeV,FunBody,
% 	      %                           FunVar,FunName,GraphsVar++GraphsPars,File,Line,GrahpsFA);
% 	     	%      _ -> % Caso de un make_fun
% 		     % 	{ModName,FunName,_} = getMFA(BFunVar),
% 		     % 	getTreeCall({c_call,cerl:get_ann(Apply),
% 		     % 	            {c_literal,[],ModName},{c_literal,[],FunName},NPars},
% 		     % 	            ets:new(env, [bag]),FreeV)
% 		% end
% 	end.


%Expresión,Entorno,Grafo,VariableLibre,IsFirstCase
%te que tornar una llista de arbres. lets i cases pels que s'ha passat
get_tree(Expr,Env,FreeV) ->
	%io:format("Expr: ~p\n",[Expr]),
	case cerl:type(Expr) of
		'apply' ->
			get_tree_apply(Expr,Env,FreeV);
		'case' ->
			get_tree_case(Expr,Env,FreeV);
		'let' ->
			Vars = cerl:let_vars(Expr),
			LetArg = cerl:let_arg(Expr),
			% io:format("LetArg: ~p\nVars: ~p\n",
			% 	[LetArg,cerl_trees:variables(LetArg)]),
			%We suppose that the letarg has not any let or case construction
			{ValueArg,FreeV,[]} = 
		     	get_tree(LetArg,Env,FreeV),
		    Deps = get_dependences(cerl_trees:variables(LetArg),Env),
		    %io:format("Deps: ~p\n",[Deps]),
		    {GraphsArg,NFreeV} = 
		    	build_graphs_and_add_bindings(Vars,Env,FreeV,ValueArg,Deps,[]),
			%{NGraphsArg,NNFreeV} = changeRepeatedIds(GraphsArg,NFreeV),
			case check_errors(ValueArg) of
			     true -> 
			     	{ValueArg,NFreeV,GraphsArg};
			     _ ->
					LetBody = cerl:let_body(Expr),
					{Value,NNFreeV,GraphBody} = 
					    get_tree(LetBody,Env,NFreeV),
					{Value,NNFreeV,GraphsArg ++ GraphBody} 
			end;
		'letrec' ->
			%les definicions poden gastar variables declarades abans? Si es aixi hi hauria que tractaro
			NewDefs = cerl:letrec_defs(Expr),
			{core,Core} = hd(ets:lookup(core,Env)),
			NCore =	cerl:c_module(cerl:module_name(Core), 
					 	cerl:module_exports(Core),
					 	cerl:module_attrs(Core),
					 	NewDefs ++ cerl:module_defs(Core)),
			ets:insert(Env,{core,NCore}),
			get_tree(cerl:letrec_body(Expr),Env,FreeV);
			% Genero un nuevo CORE de un módulo que es igual a 'Core' pero que tiene
			% la función declarada en el letrec y genero el arbol del cuerpo del letrec
		'call' ->
			case Expr of
			     {c_call,_,{c_literal,_,erlang},{c_literal,_,make_fun},_} ->
			     	{Expr,FreeV,[]};
			     _ -> 
			     	get_tree_call(Expr,Env,FreeV)
			end;
		'fun' -> 
			[{id,{_,_,FunName}},Line,{file,File}] = cerl:get_ann(Expr),
			%io:format("Previous expr: ~p\n",[Expr]),
			%io:format("\n\nVars: ~p\n\n\n",[cerl_trees:variables(Expr)]),
			% Cuidao amb lo shadowed!!!
			NExpr = 
			   apply_substitution(Expr,Env,[]), % Sustituye las variables libres
			EnvFun = ets:new(FunName,[set]),
			ets:insert(EnvFun,ets:tab2list(Env)),
			%io:format("NExpr: ~p\n",[NExpr]),
			% de la fun por sus valores
			%io:format("New expr: ~p\n",[NExpr]),
			{{anonymous_function,FunName,NExpr,File,Line,EnvFun},FreeV,[]};
		'cons' ->
			{[NHd,NTl],NFreeV,Graphs} = 
				get_tree_list([cerl:cons_hd(Expr),cerl:cons_tl(Expr)],
				            Env,FreeV),
			{cerl:c_cons(NHd,NTl),NFreeV,Graphs};
		'tuple' ->
			{NExps,NFreeV,Graphs} = 
			    get_tree_list(cerl:tuple_es(Expr),Env,FreeV),
			{cerl:c_tuple(NExps),NFreeV,Graphs};
		'try' -> 
			{ValueArg,NFreeV,GraphsArg} = 
			   get_tree(cerl:try_arg(Expr),Env,FreeV),
			%io:format("Try-Value: ~p\n",[ValueArg]),
			case ValueArg of
			     {c_literal,[],{error,TypeError}} -> 
			     	AError = [cerl:abstract(Lit) || Lit <- [error,TypeError,[]]],
			     	EVarsError = lists:zip(cerl:try_evars(Expr),AError),
			     	add_bindings_to_env(
			     		[{EVar,EValue,[],null} || {EVar,EValue} <- EVarsError],Env),
			     	{Value,NNFreeV,GraphsBody} = 
			     	    get_tree(cerl:try_handler(Expr),Env,NFreeV),
			     	{Value,NNFreeV,GraphsArg ++ GraphsBody};
			     _ ->
			        lists:map(fun(Var) -> 
			                    add_bindings_to_env([{Var,ValueArg,[],null}],Env) 
			                  end,cerl:try_vars(Expr)),
			     	{Value,NNFreeV,GraphsBody} = 
			     	   get_tree(cerl:try_body(Expr),Env,NFreeV),
			     	{Value,NNFreeV,GraphsBody}
			end;
		'catch' ->
		  % Genera la expresión azucar sintáctico equivalente y computa su árbol
			TempVar = 
			   cerl:c_var(list_to_atom("_cor_catch"++integer_to_list(FreeV))),
			TempVar1 = 
			   cerl:c_var(list_to_atom("_cor_catch"++integer_to_list(FreeV+1))),
			TempVar2 = 
			   cerl:c_var(list_to_atom("_cor_catch"++integer_to_list(FreeV+2))),
			TempVar3 = 
			   cerl:c_var(list_to_atom("_cor_catch"++integer_to_list(FreeV+3))),
			EqTry = 
			  cerl:c_try(cerl:catch_body(Expr),
			             [TempVar],TempVar,[TempVar1,TempVar2,TempVar3], 
			             cerl:c_case(
			                TempVar1,
			           	[cerl:c_clause([cerl:abstract('throw')],TempVar2),
			                 cerl:c_clause([cerl:abstract('exit')],
			                 cerl:c_tuple([cerl:abstract('EXIT'),TempVar2])),
			           	 cerl:c_clause([cerl:abstract('error')],
			           	               cerl:c_tuple([cerl:abstract('EXIT'),
			           	                             cerl:c_tuple(
			           	                               [TempVar2,TempVar3])]))
			           	])),
			get_tree(EqTry,Env,FreeV);  
%		'bitstr' ->
%			{Value,NFreeV,Roots} = 
%			   getTree(cerl:bitstr_val(Expr),Env,G,Core,FreeV,EnvAF,Trusted),
%			{cerl:c_bitstr(Value,cerl:bitstr_size(Expr),
%			              cerl:bitstr_unit(Expr),cerl:bitstr_type(Expr),
%			              cerl:bitstr_flags(Expr)),
%			NFreeV,Roots};
%		'binary' ->
%			{NExps,NFreeV,Roots} = 
%			   getTreeList(cerl:binary_segments(Expr),Env,G,Core,FreeV,EnvAF,Trusted),
%			{cerl:c_binary(NExps),NFreeV,Roots};
		'seq' ->
		         {Value,NFreeV,Graphs} =
		           get_tree(cerl:seq_arg(Expr),Env,FreeV),
		         case check_errors(Value) of
		              true -> 
		              	{Value,NFreeV,Graphs};
		              _ ->
		              	get_tree(cerl:seq_body(Expr),Env,FreeV)
		         end;
		'literal' ->
			{Expr,FreeV,[]};
		'var' -> 
			{bind_vars(Expr,Env),FreeV,[]};
		'values' -> 
			{bind_vars(Expr,Env),FreeV,[]};
		'primop' ->
		        {{c_literal,[],
		          {error,cerl:concrete(cerl:primop_name(Expr)),
		          [cerl:concrete(bind_vars(Arg,Env)) || Arg <- cerl:primop_args(Expr)]}},
		        FreeV,[]};
		_ -> throw({error,"Non treated expression",Expr}),
		     {Expr,FreeV,[]}	
	end.


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% getTreeApply(Apply,Env0,FreeV)->
% 	FunVar = cerl:apply_op(Apply),
% 	%io:format("Apply: ~p\nFunVar: ~p\nModule: ~p\nEnv0: ~p\nTrusted: ~p\n",[Apply,FunVar,cerl:module_name(Core),ets:tab2list(Env0),Trusted]),
% 	%io:format("Apply: ~p\nTrusted: ~p\n",[Apply,Trusted]),
% 	Pars = cerl:apply_args(Apply),
% 	NPars = lists:map(fun(Par) -> bindVars(Par,Env0) end,Pars),
% 	GraphsPars = lists:flatten(lists:map(fun(Par) -> get_graphs_var(Par,Env0) end,Pars)),
% 	%FunDefs = cerl:module_defs(Core),
% 	case cerl:var_name(FunVar) of
% 	     {FunName,_} ->
% 	     	getTreeCall(
% 	     	  cerl:ann_c_call(cerl:get_ann(Apply),
% 	     	              {c_literal,[],extractModuleFromAnn(cerl:get_ann(Apply))},
% 	     	              {c_literal,[],FunName},Pars),Env0,FreeV);
% 	     _ -> % Apply de una variable
% 	     	BFunVar = bindVars(FunVar,Env0),
% 	     	GraphsVar = get_graphs_var(FunVar,Env0),
% 	     	case BFunVar of
% 	     	     {anonymous_function,FunName,FunCore,File,Line,GrahpsFA} -> % Se enlaza a una función anónima
% 	     	        {c_fun,_,Args,FunBody} = FunCore,
% 	                getTreeApplyFun(Args,NPars,FreeV,FunBody,
% 	                                FunVar,FunName,GraphsVar++GraphsPars,File,Line,GrahpsFA);
% 	     	     _ -> % Caso de un make_fun
% 		     	{ModName,FunName,_} = getMFA(BFunVar),
% 		     	getTreeCall({c_call,cerl:get_ann(Apply),
% 		     	            {c_literal,[],ModName},{c_literal,[],FunName},NPars},
% 		     	            ets:new(env, [bag]),FreeV)
% 		end
% 	end.
	
% getTreeApplyFun(Args,NPars,FreeV,FunBody,FunVar,FunName,Graphs,File,Line,GrahpsFA) ->
% 	%Comprovar que no genere problemes el fet de tindre tables anidades amb el mateix nom
% 	Env = ets:new(env_temp, [bag]),
% 	createNewEnv(Args, [{NPar,[]} || NPar <- NPars], Env),
% 	%addBindingsToEnv(Env0,Env),
% 	%io:format("Env: ~p\n",[ets:tab2list(Env)]),
% 	CaseId = get(case_id),
% 	{Value,NFreeV,_} = getTree(FunBody,Env,FreeV),
% %	IsLC = % Detecta si se trata de una list comprehension
% %	  case cerl:var_name(FunVar) of
% %	       {FunName,_} ->
% %	     	  SFunName = atom_to_list(FunName), 
% %		  case SFunName of
% %			[$l,$c,$$,$^|_] -> true;
% %			_ -> false
% %		  end;
% %	       _ -> false
% %	  end,
% 	%IsLC = false,
% 	[AValue|APars] = lists:map(fun getAbstractForm/1,[Value|NPars]),
% 	%io:format("cerl:var_name(FunVar): ~p\n",[cerl:var_name(FunVar)]),
% 	AApply =  
% 	  case  cerl:var_name(FunVar) of
% %		{FunName,_} ->
% %			case IsLC of
% %			     true ->
% %			     	"";
% %			     _ -> 
% %%			     	case Trusted of
% %%			     	     true -> "";
% %%			     	     _ -> 
% %					{call,1,{remote,1,
% %					          {atom,1,cerl:concrete(cerl:module_name(Core))},
% %					          {atom,1,FunName}},APars}
% %%				end
% %			end;
% 		_ -> 
% %			""
% 			{call,1,getFunFromAbstract(File,Line),APars}
% 	  end,
% 	%io:format("Vertex's label: ~s\n",[VLabel]),
% 	case AApply of 
% 	     %"" -> {Value,NFreeV,GraphsBody};
% 	     _ -> 
% 	        G = digraph:new([acyclic]),
% 	        Context = create_context(GrahpsFA),
% 		digraph:add_vertex(G,NFreeV,
% 		                   {erl_prettypr:format({match,1,AApply,AValue},
% 		                                       [{paper, 300},{ribbon, 300}]),
% 		                    0,Context}),
% 		%[digraph:add_edge(G,NFreeV,Root) || Root <- Roots],
% 		{Value,NFreeV+1,[G|Graphs++GrahpsFA]}
% 	end.

% getTreeCall(Call,Env0,FreeV) -> 
% 	%io:format("Call : ~p\n",[Call]),
% 	ModName = cerl:concrete(bindVars(cerl:call_module(Call),Env0)),
% 	FunName = cerl:concrete(bindVars(cerl:call_name(Call),Env0)),
% 	FunArity = cerl:call_arity(Call),
% 	Args = cerl:call_args(Call),
% 	%Quitar funciones de esta lista
% 	%io:format("Args: ~p\n",[[cerl:call_module(Call),cerl:call_name(Call)|Args]]),
% 	GraphVars = lists:flatten([get_graphs_var(Var,Env0) 
% 	                           || Var <- [cerl:call_module(Call),cerl:call_name(Call)|Args]]),
% 	%io:format("GraphVars: ~p\n",[GraphVars]),
% %	io:format("FUNCTION CALL ~p:~p/~p\n",[ModName,FunName,FunArity]),
%      	BArgs = lists:map(fun(Arg) -> bindVars(Arg,Env0) end,Args),
%      	%io:format("BArgs: ~p\n",[BArgs]),
%      	NoLits = 
% 	     	case [BArg || BArg = {anonymous_function,_,_,_,_,_} <- BArgs] of
% 	     	     [] ->
% 	     	        [BArg || BArg <- BArgs,
% 	     	                 not cerl:is_literal(cerl:fold_literal(BArg))];
% 	     	     List -> List
% 	     	end,
%      	%io:format("NoLits: ~p\n",[NoLits]),
%      	case NoLits of
%      	     [] -> 
%      	     	ABArgs = [getAbstractFromCoreLiteral(cerl: fold_literal(BArg)) || BArg <- BArgs],
%      	     	%io:format("ABArgs: ~p\n",[ABArgs]),
%      	     	Value =  
% 			try
%           % Posible problema si el ya existe un módulo foo
% 			   M1 = smerl:new(foo),
% 			   {ok, M2} = 
% 			      smerl:add_func(M1, 
% 			          {function,1,bar,0,
% 		                    [{clause,1,[],[],
% 		                     [{call,1,{remote,1,{atom,1,ModName},
% 			                               {atom,1,FunName}},ABArgs}]}]}),
%                                       smerl:compile(M2,[nowarn_format]),
% 	                     foo:bar() %Genera el valor utilizando el módulo creado
% 	                               %on de fly
% 			catch
% 			   Exception:Reason -> {Exception,Reason}
% 			end,
% 		AValue = cerl:abstract(Value),
% 		%io:format("AValue: ~p\n\n",[AValue]),
% 		{AValue,FreeV,GraphVars};
% 	     _ -> 
% 	        case {ModName,FunName} of
% 	             {'erlang','is_function'} ->
% 	                case BArgs of
% 	                     [Function = {c_call,_,{c_literal,_,erlang},
% 	                      {c_literal,_,make_fun},_} | MayBeArity] ->
% 	                       {_,_,CFunArity} = getMFA(Function),
% 	                       case lists:map(fun cerl:concrete/1,MayBeArity) of
%      	                            [] ->  {{c_literal,[],true},FreeV,GraphVars};
%      	                            [CFunArity] -> {{c_literal,[],true},FreeV,GraphVars};
%      	                            _ -> {{c_literal,[],false},FreeV,GraphVars}
%      	                       end;
% %	                     [{anonymous_function,AFunName,AFunCore} | MayBeArity] ->
% %	                       {anonymous,{c_fun,_,AFunArgs,_},_,_,_} = 
% %     	                          getAnonFunc(EnvAF,AFunName,AFunCore),
% %     	                       AFunArity = length(AFunArgs),
% %     	                       case lists:map(fun cerl:concrete/1,MayBeArity) of
% %     	                            [] ->  {{c_literal,[],true},FreeV,GraphVars};
% %     	                            [AFunArity] -> {{c_literal,[],true},FreeV,GraphVars};
% %     	                            _ -> {{c_literal,[],false},FreeV,GraphVars}
% %     	                       end; 
% 	                     _ ->
% 	                       {{c_literal,[],false},FreeV,GraphVars}
% 	                end;
% 	             _ ->
% 	               -1
% %	               FileAdress = code:where_is_file(atom_to_list(ModName)++".erl"),
% %			% Busca el erl. Si no está, busca el beam (libreria de sistema) y tunea la ruta
% %			% para apuntar al ebin/ correspondiente
% %			NFileAdress = 
% %			   case FileAdress of
% %			        non_existing -> 
% %			     		NFileAdress_ = 
% %			     		   code:where_is_file(atom_to_list(ModName)++".beam"),
% %			     		case NFileAdress_ of
% %			     		     non_existing -> 
% %			     		     	throw({error,"Non existing module",ModName});
% %			     		     _ -> 
% %			     		     	RelPath = "ebin/" ++ 
% %			     		     	           atom_to_list(ModName) ++ ".beam",
% %			     		     	NRelPath = "src/" ++ 
% %			     		     	           atom_to_list(ModName) ++ ".erl",
% %			     		     	PrevPath = 
% %			     		     	  lists:sublist(NFileAdress_,
% %			     		     	     1,length(NFileAdress_)-length(RelPath)),
% %			     		     	PrevPath ++ NRelPath
% %			     		end;
% %			     	_ -> FileAdress
% %			   end,
% %	               ModCore = core_module(NFileAdress),
% %	               %Faltara añadir las varaibles del call
% %	               getTreeApply(cerl:ann_c_apply(cerl:get_ann(Call),
% %	                            cerl:c_var({FunName,FunArity}),Args),
% %	                     Env0,FreeV)
% 	        end
	        
% 	 end.
	
% getTreeCase(Expr,Env,FreeV) -> 
% 	Args = cerl:case_arg(Expr),
% 	{ArgsValue,NFreeV,GraphsArgs} = getTree(Args,Env,FreeV),
% 	{NGraphsArgs,NFreeV__} = changeRepeatedIds(GraphsArgs,NFreeV),
% 	%io:format("Args: ~p\nEnv: ~p\n",[Args,ets:tab2list(Env)]),
% 	BArgs_ = bindVars(ArgsValue,Env),
% 	BArgs = 
% 		case cerl:type(BArgs_) of
% 			values -> cerl:values_es(BArgs_);
% 			_ -> [BArgs_]
% 		end,
% 	[Line,{file,FileName}] = cerl:get_ann(Expr),
% 	AbstractCase = getCaseFromAbstract(FileName,Line),
%         Clauses = cerl:case_clauses(Expr),
% 	{Clause,ClauseBody,Bindings,NFreeV_,GraphsClauses} = 
% 	  getClauseBody(Clauses,Clauses,NGraphsArgs,AbstractCase,BArgs,Env,NFreeV__),
% 	ClauseNumber = getClauseNumber(Clauses,Clause,1),
% %	ArgPrimOp = 
% %	  element(3,lists:nth(1,
% %	          cerl:primop_args(cerl:clause_body(lists:nth(
% %	           length(Clauses),Clauses))))),
% %        IsFunction =
% %          is_list(ArgPrimOp) andalso 
% %	  lists:member(cerl:abstract(function_clause),ArgPrimOp),
% 	%io:format("CASE: ~p\n",[getCaseFromAbstract(FileName,Line)]),
% 	{NGraphsClauses,NNFreeV_} = changeRepeatedIds(GraphsClauses++NGraphsArgs,NFreeV_),
% 	%io:format("Graphs clauses: ~p\n",[NGraphsClauses]),
% %	io:format("getCaseFromAbstract(FileName,Line): ~p\n",
% %	          [getCaseFromAbstract(FileName,Line)]),
% 	{GraphCase,NNFreeV} = 
% 	   %o es una funció
% 	   case AbstractCase of
% 	        [{ACase,Type}|_] ->
% 	          G = digraph:new([acyclic]),
% 	          add_graphs_to_graph(G,NGraphsClauses),
% %	          Vars = cerl_trees:variables(Args),
% %	          io:format("Vars: ~p\n",[Vars]),
% %	          BVars = [{Var,bindVars(cerl:c_var(Var),Env)} || Var <- Vars],
% %	          NameValue = [{Name,getAbstractForm(BVar)} || {Name,BVar} <- BVars],
% %	          %Plantejarse ficar açi \n i ficar \l sols al dot
% %	          CurrentEnv = "[" ++ stringEnv(NameValue) ++ "]",
% 		  %io:format("GraphsArgs: ~p\n",[GraphsArgs]),
% 		  Context = create_context(NGraphsClauses),%++NGraphsGuard),
%                   digraph:add_vertex(G,NNFreeV_,
%                    {Type ++" expression:\\l"++changeNewLines(erl_prettypr:format(ACase))++
%                     "\\l"++"enters in the "++edd_lib:get_ordinal(ClauseNumber) 
%                     ++ " clause",%with:\\l" ++ CurrentEnv++"\\l",
%                     0,Context}), 
%                    [digraph:add_edge(G,NNFreeV_,edd_lib:look_for_root(G_)) 
% 		    || G_ <- NGraphsClauses],
%                    Graphs = [G],%++NGraphsGuard,
% 	           {Graphs,NNFreeV_+1};
% 	        [] ->
% 	           {[],NNFreeV_} 
% 	   end,
% 	%io:format("GraphCase: ~p\n",[GraphCase]),
% 	%io:format("GraphsArgs: ~p\n",[GraphsArgs]),
% 	%io:format("Bindings: ~p\n",[Bindings]),
% 	NNNFreeV = buildGraphAndAddBinding(Bindings,NGraphsArgs,Env,NNFreeV),  	
% 	{Value,NNNNFreeV,GraphBody} = getTree(ClauseBody,Env,NNNFreeV),
% 	%Si es lo mismo de arrriba borrar la ultima linea
% 	{Value,NNNNFreeV,GraphCase ++ GraphBody}.
	
% getTreeList([E|Es],Env,FreeV) ->
% 	{NE,NFreeV,GraphsH} = getTree(bindVars(E,Env),Env,FreeV),
% 	{NEs,NNFreeV,GraphsT} = getTreeList(Es,Env,NFreeV),
% 	{[NE|NEs],NNFreeV,GraphsH++GraphsT};
% getTreeList([],_,FreeV) ->
% 	{[],FreeV,[]}.
	
% % 1.- Construye la 1ª cláusula sin guardas, el resto igual
% % 2.- Mira si ha elegido la 1ª cláusula
% % 3.- a) Si el la primera, comprueba que la guarda se cumple. Si es así, 
% %        devuelve esa cláusula como la elegida. Si no, prueba con la siguiente.
% % 3.- b) Si no, prueba con la siguiente
% %% Explicación: cerl_clauses:reduce(), que devuelve la cláusula que se elige
% %% en un case, no funciona con las guardas
% %getClauseBody([Clause | Clauses],BArgs,Env,FreeV) ->
% %	NClause = cerl:c_clause(cerl:clause_pats(Clause), cerl:clause_body(Clause)),
% %	case cerl_clauses:reduce([NClause| Clauses], BArgs) of
% %	     {true, {{c_clause, _, _, _, ClauseBody}, Bindings}} -> 
% %		case cerl:clause_body(Clause) of
% %		     ClauseBody -> 
% %		        NEnv = ets:new(env_guard,[bag]),
% %		        ets:insert(NEnv,ets:tab2list(Env)),
% %		        %io:format("Bindings: ~p\n",[Bindings]),
% %		        {VarsPattern,ValuesPattern} = lists:unzip(Bindings),
% %		        createNewEnv(VarsPattern, [{VP,[]} || VP <- ValuesPattern], NEnv),
% %		     	{GuardValue,NFreeV,Graphs} = 
% %		     		getTree(cerl:clause_guard(Clause),NEnv,FreeV),
% %		        %io:format("Guard: ~p\nGraphs: ~p\n",[cerl:clause_guard(Clause),Graphs]),
% %		     	case cerl:concrete(GuardValue) of
% %		     	     true -> {Clause,ClauseBody,Bindings,NFreeV,Graphs};
% %		     	     false -> getClauseBody(Clauses,BArgs,Env,FreeV)
% %		     	end;
% %		     _ -> getClauseBody(Clauses,BArgs,Env,FreeV)
% %		end;
% %	      _ -> getClauseBody(Clauses,BArgs,Env,FreeV)
% %	end;
% %getClauseBody([],_,_,_) -> throw({error,"Non matching clause exists"}).


% getClauseBody([Clause | Clauses],AllClauses,GraphsArgs,AbstractCase,BArgs,Env,FreeV) ->
% 	NClause = cerl:c_clause(cerl:clause_pats(Clause), cerl:clause_body(Clause)),
% 	case cerl_clauses:reduce([NClause| Clauses], BArgs) of
% 	     {true, {{c_clause, _, _, _, ClauseBody}, Bindings}} -> 
% 		case cerl:clause_body(Clause) of
% 		     ClauseBody -> 
% 		        NEnv = ets:new(env_guard,[bag]),
% 		        ets:insert(NEnv,ets:tab2list(Env)),
% 		        %io:format("Bindings: ~p\n",[Bindings]),
% 		        {VarsPattern,ValuesPattern} = lists:unzip(Bindings),
% 		        createNewEnv(VarsPattern, [{VP,[]} || VP <- ValuesPattern], NEnv),
% 		     	{GuardValue,NFreeV,GraphsGuard} = 
% 		     		getTree(cerl:clause_guard(Clause),NEnv,FreeV),
% 		        %io:format("Guard: ~p\nGraphs: ~p\n",[cerl:clause_guard(Clause),Graphs]),
% 		     	case cerl:concrete(GuardValue) of
% 		     	     true -> 
% 		     	     	{GraphGuardSucceeds,NFreeV_} = 
% 			      	   case AbstractCase of
% 			      	        [{ACase,Type}|_] ->
% 			      	          ClauseNumber = getClauseNumber(AllClauses,Clause,1),
% 			      	          Context = create_context(GraphsGuard),
% 			      	          G = digraph:new([acyclic]),
% 			      	          add_graphs_to_graph(G,GraphsGuard),
% 				       	  digraph:add_vertex(G,NFreeV,
% 			                   {Type ++" expression:\\l"
% 			                    ++changeNewLines(erl_prettypr:format(ACase))++
% 			                    "\\l"++"the guard of the "
% 			                    ++edd_lib:get_ordinal(ClauseNumber) 
% 			                    ++ " clause succeeds",
% 			                    0,Context}),
% 			                  [digraph:add_edge(G,NFreeV,edd_lib:look_for_root(G_)) 
% 			                   || G_ <- GraphsGuard],
% 			                  {[G],NFreeV+1}
% 			                  ;
% 			      	        [] ->
% 			      	          {[],NFreeV}
% 			      	   end,
% 		     	     	{Clause,ClauseBody,Bindings,NFreeV_,GraphGuardSucceeds};
% 		     	     false ->
% 			      	 {GraphGuardFailed,NFreeV_} = 
% 			      	   case AbstractCase of
% 			      	        [{ACase,Type}|_] ->
% 			      	          ClauseNumber = getClauseNumber(AllClauses,Clause,1),
% 			      	          Context = create_context(GraphsGuard),
% 			      	          G = digraph:new([acyclic]),
% 			      	          add_graphs_to_graph(G,GraphsGuard),
% 				       	  digraph:add_vertex(G,NFreeV,
% 			                   {Type ++" expression:\\l"
% 			                    ++changeNewLines(erl_prettypr:format(ACase))++
% 			                    "\\l"++"the guard of the "
% 			                    ++edd_lib:get_ordinal(ClauseNumber) 
% 			                    ++ " clause fails",
% 			                    0,Context}),
% 			                  [digraph:add_edge(G,NFreeV,edd_lib:look_for_root(G_)) 
% 			                   || G_ <- GraphsGuard],
% 			                  {NG,NNFreeV_} = 
% 			                    changeRepeatedIds([G|GraphsArgs],NFreeV+1),
% 		     	  		  {build_pattern_clause_graph(Clause,Clauses,
% 		     	  			  AllClauses,AbstractCase,NG,
% 		     	  			  NNFreeV_,BArgs,Env,true),NNFreeV_+1}
% 			                  ;
% 			      	        [] ->
% 			      	          {[],NFreeV}
% 			      	   end,
% 			       	{SelectedClause,NClauseBody,NBindings,NNFreeV,Graphs} =
% 			       	   getClauseBody(Clauses,AllClauses,GraphsArgs,AbstractCase,
% 			       	                 BArgs,Env,NFreeV_),
% 			       	%io:format("Graphs: ~p\n",[GraphGuardFailed]),
% 			       	{SelectedClause,NClauseBody,NBindings,
% 			       	 NNFreeV,GraphGuardFailed++Graphs}
% 		     	end;
% 		     _ -> 
% 		     	GraphPatternFailed = 
% 		     	  build_pattern_clause_graph(Clause,Clauses,AllClauses,
% 		     	     AbstractCase,GraphsArgs,FreeV,BArgs,Env,false),
% 		     	{SelectedClause,NClauseBody,Bindings,NFreeV,Graphs} =
% 		  	   getClauseBody(Clauses,AllClauses,GraphsArgs,AbstractCase,
% 		                 BArgs,Env,FreeV+1),
% 			{SelectedClause,NClauseBody,Bindings,NFreeV,GraphPatternFailed++Graphs}
% %		      	 GraphPatternFailed = 
% %		      	   case AbstractCase of
% %		      	        [{ACase,Type}|_] ->
% %		      	          ClauseNumber = getClauseNumber(AllClauses,Clause,1),
% %		      	          Context = create_context(GraphsArgs),
% %		      	          G = digraph:new([acyclic]),
% %		      	          add_graphs_to_graph(G,GraphsArgs),
% %			       	  digraph:add_vertex(G,FreeV,
% %		                   {Type ++" expression:\\l"
% %		                    ++changeNewLines(erl_prettypr:format(ACase))++
% %		                    "\\l"++"the pattern of the "
% %		                    ++edd_lib:get_ordinal(ClauseNumber) 
% %		                    ++ " clause does not match",
% %		                    0,Context}),
% %		                  [digraph:add_edge(G,FreeV,edd_lib:look_for_root(G_)) 
% %		                   || G_ <- GraphsArgs],
% %		                  [G];
% %		      	        [] ->
% %		      	          []
% %		      	   end,
% %		       	{SelectedClause,NClauseBody,Bindings,NFreeV,Graphs} =
% %		       	   getClauseBody(Clauses,AllClauses,GraphsArgs,AbstractCase,
% %		       	                 BArgs,Env,FreeV+1),
% %		       	%io:format("Graphs: ~p\n",[GraphPatternFailed]),
% %		       	{SelectedClause,NClauseBody,Bindings,NFreeV,GraphPatternFailed++Graphs}
% 		end;
% 	      _ -> 
% %	      	io:format("ENTRA: ~p\n",[Clause]),
% %	      	getClauseBody(Clauses,AllClauses,GraphsArgs,AbstractCase,BArgs,Env,FreeV)
% 		GraphPatternFailed = 
% 		  build_pattern_clause_graph(Clause,Clauses,AllClauses,
% 		    AbstractCase,GraphsArgs,FreeV,BArgs,Env,false),
% 		{SelectedClause,NClauseBody,Bindings,NFreeV,Graphs} =
% 		   getClauseBody(Clauses,AllClauses,GraphsArgs,AbstractCase,
% 		                 BArgs,Env,FreeV+1),
% 		{SelectedClause,NClauseBody,Bindings,NFreeV,GraphPatternFailed++Graphs}
% 	end;
% getClauseBody([],_,_,_,_,_,_) -> throw({error,"Non matching clause exists"}).
	
	
% build_pattern_clause_graph(Clause,Clauses,AllClauses,AbstractCase,
%                            GraphsArgs,FreeV,BArgs,Env,Enters) ->
%         SEnters = 
%           case Enters of
%                true -> "enters";
%                false -> "does not enter"
%           end,
% 	case AbstractCase of
% 	    [{ACase,Type}|_] ->
% 	      ClauseNumber = getClauseNumber(AllClauses,Clause,1),
% 	      Context = create_context(GraphsArgs),
% 	      G = digraph:new([acyclic]),
% 	      add_graphs_to_graph(G,GraphsArgs),
% 		digraph:add_vertex(G,FreeV,
% 		        {Type ++" expression:\\l"
% 		         ++changeNewLines(erl_prettypr:format(ACase))++
% 		         "\\l"++SEnters++" in the "
% 		         ++edd_lib:get_ordinal(ClauseNumber) 
% 		         ++ " clause",
% 		         0,Context}),
% 	       [digraph:add_edge(G,FreeV,edd_lib:look_for_root(G_)) 
% 	        || G_ <- GraphsArgs],
% 	       [G];
% 	    [] ->
% 	      []
% end.

	

% core_module(File) ->
% 	{ok,_,Core} = compile:file(File,[to_core,binary,no_copt]),
% 	Core.
    
% % Core es el CORE del módulo foo que tiene bar() -> Expr
% % extractCall devuelve únicamente el CORE de Expr (o quizá del case que lo contiene)
% extractCall(Core) ->
% 	{c_module,_,_,_,_,FunDefs} = Core,
% 	[{c_fun,_,_,FunBody}|_] = 
% 		[FunBody_ || {{c_var,_,FunName},FunBody_} <- FunDefs, FunName == {bar,0}],
% 	[{c_clause,_,_,_,Call}|_] = cerl:case_clauses(FunBody),
% 	Call.	     	
    
% get_graphs_var(Var,Env) ->
% 	%io:format("Var: ~p\n",[Var]),
% 	case cerl:type(Var) of
% 	     'var' ->
% 	        VarName = cerl:var_name(Var),
% 	     	case VarName of
% 	     	     {FunName,Arity} -> 
% 	     	     	[];
% 	     	     _ ->
% 	     		{VarName,{_,Graphs}} = hd(ets:lookup(Env,VarName)),
% 	     		Graphs
% 	     	end;
% 	     _ -> []
% 	end.
    
% bindVars(Expr,Env) ->
% 	%io:format("Expr: ~p\nEnv: ~p\n",[Expr,ets:tab2list(Env)]),
% 	case Expr of
% 	     {anonymous_function,_,_,_,_,_} -> Expr;
% 	     _ ->
% 		case cerl:type(Expr) of
% 		     'var' -> 
% 		     	VarName = cerl:var_name(Expr),
% 		     	case VarName of
% 		     	     {FunName,Arity} -> 
% 		     	     	[_,{file,FileName},_] = cerl:get_ann(Expr),
% 		     	     	{ModName,_} = lists:split(length(FileName)-4,FileName),
% 		     	     	MFArgs = 
% 		     	     	    [{c_literal,[],list_to_atom(ModName)},
%            			     {c_literal,[],FunName},
%           		             {c_literal,[],Arity}],
% 		     	     	{c_call,[],{c_literal,[],erlang},{c_literal,[],make_fun},MFArgs};
% 		     	     _ ->
% 		     		{VarName,{Value,_}} = hd(ets:lookup(Env,VarName)),
% 		     		case Value of
% 		     	             {anonymous_function,_,_,_,_,_} -> Value;
% 		     	             _ -> cerl:unfold_literal(Value)
% 		     	        end
% 		     	end;
% 		     'values' -> 
% 		     	Values = cerl:values_es(Expr),
% 		     	BValues = lists:map(fun(Var) -> bindVars(Var,Env) end,Values),
% 		     	{c_values,cerl:get_ann(Expr),BValues};
% 		    'tuple' -> 
% 		    	NExps = [bindVars(E,Env) || E <- cerl:tuple_es(Expr)],
% 		    	cerl:c_tuple(NExps);
% 		    'cons' -> 
% 		    	[NHd,NTl] = [bindVars(E,Env) || 
% 		    	             E <- [cerl:cons_hd(Expr),cerl:cons_tl(Expr)]],
% 		    	cerl:c_cons(NHd,NTl);
% 		     _ -> Expr
% 		 end
% 	 end.

% getAbstractFromCoreLiteral(Lit) ->
% 	{c_literal,_,Lit_} = Lit, 
% 	{ok,[ALit|_]} = edd_lib:parse_expr(lists:flatten(io_lib:format("~w",[Lit_])++".")),
% 	ALit.
	
% getAbstractForm({anonymous_function,_,_,File,Line,_}) -> 
% 	getFunFromAbstract(File,Line);
% getAbstractForm(Par_) -> 
% 	Par = cerl:fold_literal(Par_),
% 	case cerl:is_literal(Par) of
% 		true -> 
% 			getAbstractFromCoreLiteral(Par);
% 		_ -> 
% 			{ModName_,FunName_,FunArity_} = getMFA(Par),
% 			{'fun',1,
% 			{function,
% 			{atom,1,ModName_},
% 			{atom,1,FunName_},
% 			{integer,1,FunArity_}}}
% 	end.

% getMFA(Function) ->
% 	%io:format("Function: ~p",[Function]),
% 	{c_call,_,{c_literal,_,erlang},{c_literal,_,make_fun},MFA} = Function,
% 	[{c_literal,_,ModName},{c_literal,_,FunName},{c_literal,_,FunArity}] = MFA,
% 	{ModName,FunName,FunArity}.
	      	
% createNewEnv([{c_var,_,VarName}|TailArgs],[Value|TailPars],Env) ->
% 	ets:insert(Env,{VarName,Value}),
% 	createNewEnv(TailArgs,TailPars,Env);
% createNewEnv([],[],_) -> ok.

% addBindingsToEnv([{{c_var,_,VarName},Value,Gs}| TailBindings],Env) ->
% 	ets:insert(Env,{VarName,{Value,Gs}}),
% 	addBindingsToEnv(TailBindings,Env);
% addBindingsToEnv([{VarName,Value,Gs}| TailBindings],Env) ->
% 	ets:insert(Env,{VarName,{Value,Gs}}),
% 	addBindingsToEnv(TailBindings,Env);
% addBindingsToEnv([],_) -> ok.

% buildGraphAndAddBinding([{Var,Value}|Vars],Graphs,Env,FreeV) ->
% 	VarName = cerl:var_name(Var),
% 	case atom_to_list(VarName) of
% 	     [$c,$o,$r | _] -> 
% 	     	addBindingsToEnv([{Var,Value,Graphs}],Env),
% 	     	buildGraphAndAddBinding(Vars,Graphs,Env,FreeV); 
% 	     _ -> 
% 	     	G = digraph:new([acyclic]),
% 		add_graphs_to_graph(G,Graphs),
% 	        AValue = getAbstractForm(Value),
% 		AVar = {var,1,VarName},
% 		%io:format("AValue: ~p\nAVar: ~p\n",[AValue,AVar]),
% 		Context = create_context(Graphs),
% 		%io:format("Context: ~s\n",[Context]),
% 		digraph:add_vertex(G,FreeV,
% 	                  {erl_prettypr:format({match,1,AVar,AValue},
% 	                                      [{paper, 300},{ribbon, 300}]),
% 	                                      Var,Context}),
% 		[digraph:add_edge(G,FreeV,edd_lib:look_for_root(G_)) || G_ <- Graphs],
% 	        addBindingsToEnv([{Var,Value,[G]}],Env),
% 	        buildGraphAndAddBinding(Vars,Graphs,Env,FreeV+1) 
% 	end;
% buildGraphAndAddBinding([],_,_,FreeV) -> FreeV.

% add_graphs_to_graph(G,Graphs) ->
% 	[begin 
% 	  {V,Label} = digraph:vertex(G_,V),
% %	  {StrLabel,_} = Label,
% %	  NLabel = {StrLabel++ ", with: "++ Context,0},
% 	  digraph:add_vertex(G,V,Label) 
% 	 end || G_ <- Graphs,V <- digraph:vertices(G_)],
% 	[digraph:add_edge(G,V1,V2) || G_ <- Graphs,V1 <- digraph:vertices(G_),
% 	                              V2 <- digraph:out_neighbours(G_, V1)].

% create_context(Graphs) ->
% 	Roots = [{G,edd_lib:look_for_root(G)} || G <- Graphs],
% 	Context = 
% 	  [begin
% 	     {Root,Label} = digraph:vertex(G,Root),
% 	     {StrLabel,_,_} = Label,
% 	     case StrLabel of
% 	          [$C,$a,$s,$e|_] -> "";
% 	          [$I,$f|_] -> "";
% 	          _ -> StrLabel
% 	     end
% 	   end || {G,Root} <- Roots],
% 	create_context_string(Context).
	
% create_context_string(Context0) ->
% 	Context = lists:filter(fun(Str) -> Str =/= "" end,Context0),
% 	case Context of
% 	     [] -> [];
% 	     _ -> 
% 	       NContext = 
% 	          "["++
% 	          tl(tl(lists:foldl(fun(V, Pre) -> Pre ++ ", " ++ V end, "", Context)))
% 	          ++"]",
% 	       io_lib:format("~s",[NContext])
% 	end.

         
% changeRepeatedIds(Gs,FreeV) ->
% 	Roots = [{G,edd_lib:look_for_root(G)} || G <- Gs],
% 	NGs = 
% 	  [begin 
% 	     {Root,Label} = digraph:vertex(G,Root),
% 	     {StrLabel,_,_} = Label,
% 	     {G,StrLabel}
% 	   end || {G,Root} <- Roots],
% 	%io:format("NGs: ~p\n",[NGs]),
% 	WhitoutRepeated_ = 
% 	   lists:foldl(fun(Lbl = {G,StrLabel}, Acc) -> 
% 	                   case [StrLabel_ || {_,StrLabel_} <- Acc, StrLabel_ =:= StrLabel] of
% 	                        [] -> [Lbl | Acc];
% 	                        _ -> Acc
% 	                   end
% 	               end,[],NGs),
% 	%io:format("WhitoutRepeated_: ~p\n",[WhitoutRepeated_]),
% 	WhitoutRepeated = [G || {G,_} <- WhitoutRepeated_],
%         changeRepeatedIds_(WhitoutRepeated,FreeV,[]). 
         
% changeRepeatedIds_([G|Gs],FreeV,Acc) ->
% %        io:format("G:~p\n",[G]),
% %        io:format("vertices(G):~p\n",[lists:sort(digraph:vertices(G))]),
% %        io:format("Acc:~p\n",[lists:sort(Acc)]),
% %        io:format("FreeV:~p\n",[FreeV]),
% 	Intersection = 
% 	   sets:to_list(sets:intersection(sets:from_list(digraph:vertices(G)),
% 	                                  sets:from_list(Acc))),
% 	{NG,NFreeV} = 
% 	   case Intersection of
% 	        [] -> 
% 	           {G,FreeV};
% 	        _ -> 
% 	           {Substitution,NFreeV_} = createSubstitution(Intersection,FreeV),
% 	           NG_ = digraph:new([acyclic]),
% 	           Vertices = [digraph:vertex(G,V) || V <- digraph:vertices(G)],
% 	           Edges = [{V1,V2} || V1 <- digraph:vertices(G),
% 	                               V2 <- digraph:out_neighbours(G, V1)],
% 	           [case [NV || {V_,NV} <- Substitution, V_ =:= V] of
% 	                 [] -> digraph:add_vertex(NG_,V,Label);
% 	                 [NV] -> digraph:add_vertex(NG_,NV,Label)
% 	            end || {V,Label} <- Vertices], 
% 	           [begin
% 	             NV1 = 
% 	               case [NV1_ || {V1_,NV1_} <- Substitution, V1_ =:= V1] of
% 	                    [] -> V1;
% 	                    [NV1_] -> NV1_
% 	               end, 
% 	             NV2 = 
% 	               case [NV2_ || {V2_,NV2_} <- Substitution, V2_ =:= V2] of
% 	                    [] -> V2;
% 	                    [NV2_] -> NV2_
% 	               end, 
% 	             digraph:add_edge(NG_,NV1,NV2)      
% 	            end || {V1,V2} <- Edges], 
%          	   {NG_,NFreeV_}
% 	   end,
% 	   {NGs,NNFreeV} = changeRepeatedIds_(Gs,NFreeV,Acc++digraph:vertices(NG)),
% 	   {[NG|NGs],NNFreeV};
% changeRepeatedIds_([],FreeV,_) -> {[],FreeV}.

% createSubstitution([V|Vs],Free) ->
% 	{Subs,NFree} = createSubstitution(Vs,Free+1),
% 	{[{V,Free}|Subs],NFree};
% createSubstitution([],Free) -> {[],Free}.

% getFunFromAbstract(File,Line) -> 
% 	{ok,Abstract} = smerl:for_file(File),
% 	[AFun|_] =
% 	     lists:flatten(
% 		[erl_syntax_lib:fold(fun(Tree,Acc) -> 
% 					%io:format("{Line,Tree}: ~p\n",[{Line,Tree}]),
% 		               		case Tree of 
% 		               	    	     {'fun',Line,{clauses,_}}->
% 		               	    		[Tree|Acc];
% 		               	    	     _ -> 
% 		               	    		Acc
% 		               		end
% 			    	     end, [], Form)||Form<-smerl:get_forms(Abstract)]),		    
% 	AFun.


% getCaseFromAbstract(File,Line) -> 
% 	{ok,Abstract} = smerl:for_file(File),
% 	lists:flatten(
% 		[erl_syntax_lib:fold(fun(Tree,Acc) -> 
% 					%io:format("{Line,Tree}: ~p\n",[{Line,Tree}]),
% 		               		case Tree of 
% 		               	    	     {'case',Line,_,_} ->
% 		               	    		[{Tree,"Case"}|Acc];
% 		               	             {'if',Line,_} ->
% 		               	    		[{Tree,"If"}|Acc];
% 		               	    	     _ -> 
% 		               	    		Acc
% 		               		end
% 			    	     end, [], Form)||Form<-smerl:get_forms(Abstract)]).


% extractModuleFromAnn([_,{file,File}]) ->
% 	[_,_,_,_|ModName_] = lists:reverse(File),
% 	list_to_atom(lists:reverse(ModName_)).
	
% check_errors(Value) -> 
%          	%possiblement falten mes tipos d'errors.
% 	case Value of
% 	     {c_literal,[],{error,_}} -> true;
% 	     _ -> false
% 	end.
	
% getAnonFunc(EnvAF,FunName,FunCore) ->
% 	getAnonFunc(ets:lookup(EnvAF,FunName),FunCore).
	
% getAnonFunc([{_,AF = {anonymous_function,_,_,_,_,_}}|_],FunCore) -> AF;
% getAnonFunc([_|AFs],FunCore) -> getAnonFunc(AFs,FunCore);
% getAnonFunc([],_)->{}.

% getClauseNumber([Clause|_],Clause,N) -> N;
% getClauseNumber([_|Clauses],Clause,N) -> getClauseNumber(Clauses,Clause,N+1);
% getClauseNumber([],_,_) -> -1.

% changeNewLines([10|Chars]) ->
% 	[$\\,$l|changeNewLines(Chars)];
% changeNewLines([Other|Chars]) ->
% 	[Other|changeNewLines(Chars)];
% changeNewLines([]) ->
% 	[].

% stringEnv([{VarName,AValue}]) ->
% 	atom_to_list(VarName)++ " = "
% 	++ erl_prettypr:format(AValue,[{paper, 300},{ribbon, 300}]);
% stringEnv([{VarName,AValue}|Tail]) ->
% 	atom_to_list(VarName)++ " = "
% 	++ erl_prettypr:format(AValue,[{paper, 300},{ribbon, 300}])
% 	++ ", " ++ stringEnv(Tail);
% stringEnv([]) -> "".


% get_fundef_and_vars_clause(ModName,FunName,Arity,Clause) ->
% 	{ok,M} = smerl:for_file(atom_to_list(ModName) ++ ".erl"),
% 	FunctionDef = 
% 	    hd([FunctionDef_ || 
%               	FunctionDef_ = {function,_,FunName_,Arity_,_} <- smerl:get_forms(M),
% 		FunName_ =:= FunName, Arity_ =:= Arity]),
% 	{function,_,FunName,Arity,Clauses} = FunctionDef,
% 	io:format("Clauses: ~p\nClause: ~p\n",[length(Clauses),Clause]),
% 	SelectedClause = lists:nth(Clause, Clauses),
% 	Patterns = erl_syntax:clause_patterns(SelectedClause),
% 	{FunctionDef,length(Clauses),
% 	 sets:to_list(sets:union([erl_syntax_lib:variables(Pattern) || Pattern <- Patterns]))}.

% applySubstitution(Expr,Env,Bindings) ->
% 	cerl_trees:mapfold(
% 		fun(T,Acc)->
% 			case cerl:type(T) of
% 			     'var' -> 
% 			     	case cerl:var_name(T) of
% 			     	     {_,_} -> {T,Acc};
% 			     	     VN ->
% 			     	     	case ets:lookup(Env,VN) of
% 			     	     	     [] -> 
% 			     	     	     	Values = 
% 			     	     	     	  [Value || {{c_var,_,VarName},Value} <- Bindings,
% 			     	     	     	            VarName =:= VN],
% 			     	     	     	case Values of
% 			     	     	     	     [] -> {T,Acc};
% 			     	     	     	     [Value|_] -> 
% 			     	     	     	     	{Value,Acc}
% 			     	     	     	end;
% 			     	     	     [{_,{Value,Graphs}}|_] ->
% 			     	     	     	{Value,Graphs++Acc}
% 			     	     	end
% 			     	end;
% 			     _ -> {T,Acc}
% 			end
% 		end,[],Expr).

