%%%    Copyright (C) 2013 Salvador Tamarit <stamarit@dsic.upv.es>
%%%
%%%    This file is part of Erlang Declarative Debugger.
%%%
%%%    Erlang Declarative Debugger is free software: you can redistribute it and/or modify
%%%    it under the terms of the GNU General Public License as published by
%%%    the Free Software Foundation, either version 3 of the License, or
%%%    (at your option) any later version.
%%%
%%%    Erlang Declarative Debugger is distributed in the hope that it will be useful,
%%%    but WITHOUT ANY WARRANTY; without even the implied warranty of
%%%    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
%%%    GNU General Public License for more details.
%%%
%%%    You should have received a copy of the GNU General Public License
%%%    along with Erlang Declarative Debugger.  If not, see <http://www.gnu.org/licenses/>.

%%%-----------------------------------------------------------------------------
%%% @author Salvador Tamarit <stamarit@dsic.upv.es>
%%% @copyright 2013 Salvador Tamarit
%%% @version 0.1
%%% @doc Erlang Declarative Debugger auxiliary library. This module contains 
%%%      auxiliary functions needed by the Erlang Declarative Debugger 'edd'.
%%% @end
%%%-----------------------------------------------------------------------------

-module(edd_zoom_lib).

-export([parse_expr/1, dot_graph_file/2, ask/2, core_module/1, look_for_root/1]).

%%------------------------------------------------------------------------------
%% @doc Parses a string as if it were an expression. Returns a unitary list 
%%      containing the abstract representation of the expression.
%% @end
%%------------------------------------------------------------------------------
-spec parse_expr(Func::string()) -> {ok, [erl_parse:abstract_expr()]} | {error, parse_error}.
parse_expr(Func) ->
    case erl_scan:string(Func) of
	{ok, Toks, _} ->
	    case erl_parse:parse_exprs(Toks) of
		{ok, _Term} = Res ->
		    Res;
		_Err ->
		    {error, parse_error}
	    end;
	_Err ->
	    {error, parse_error}
    end.

%%------------------------------------------------------------------------------
%% @doc Compiles the Erlang program 'File' into Core Erlang and returns the 
%%      resulting Core program as a binary.
%%      
%% @end
%%------------------------------------------------------------------------------
-spec core_module( File :: string()) -> binary().    
core_module(File) ->
	{ok,_,Core} = compile:file(File,[to_core,binary,no_copt]),
	Core.


look_for_root(G)->
	case digraph:no_vertices(G) of
	     0 -> no;
	     1 -> hd(digraph:vertices(G));
	     _ -> hd([V||V <- digraph:vertices(G), digraph:in_degree(G, V)==0])
	end.

%%------------------------------------------------------------------------------
%% @doc Traverses the tree 'G' asking the programmer until it finds the buggy 
%%      node. The tree 'G' must be a digraph representing the abbreviated proof 
%%      tree of the evaluation of an expression that yields an incorrect value.
%%      When it finds the buggy node, shows the function rule responsible for
%%      the incorrect value. The strategy followed is indicated by its second
%%      argument.      
%% @end
%%------------------------------------------------------------------------------
-spec ask( G :: digraph(), Strategy :: top_down | divide_query) -> ok.
ask(G,Strategy)->
	Root = look_for_root(G),
	Vertices = digraph:vertices(G) -- [Root],
	ask_about(G,Strategy,Vertices,[],[Root]).
	

ask_about(G,Strategy,Vertices,Correct0,NotCorrect0) -> 
	{Correct,NotCorrect,Unknown,_,NStrategy} = 
	   asking_loop(G,Strategy,Vertices,Correct0,NotCorrect0,[],[],-1),
	case NotCorrect of
	     [-1] ->
	     	io:format("Debugging process finished\n");
	     _ -> 
	        NotCorrectVertexs = [NCV || NCV <- NotCorrect, 
	                                   (digraph:out_neighbours(G, NCV)--Correct)==[] ],
	        case NotCorrectVertexs of
	             [] ->
	             	io:format("Not enough information.\n"),
	             	NotCorrectWithUnwnownVertexs = 
					  [NCV || NCV <- NotCorrect, 
			                          (digraph:out_neighbours(G, NCV)--(Correct++Unknown))=:=[]],
	                Maybe0 = 
	                         [U || U <- Unknown, 
	                               NCV <- NotCorrectWithUnwnownVertexs,
	                               lists:member(U,digraph:out_neighbours(G, NCV))],
	                Maybe = find_unknown_children(G,Unknown,Maybe0),
					case get_answer("Do you want to try to answer"
					     ++ " the needed information? [y/n]: ",[y,n]) of
					     y -> 
					     	ask_about(G,NStrategy,Maybe,Correct,NotCorrect);
					     n -> 
			               [print_buggy_node(G,V,
			                "This piece of code could contain an error") 
			                || V <- NotCorrectWithUnwnownVertexs],
			               [print_buggy_node(G,V,
			                 "This piece of code has not been answered and could contain an error") 
					                || V <- Maybe]
					end;
	             [NotCorrectVertex|_] ->
	               	print_buggy_node(G,NotCorrectVertex,
	               	 "Piece of code that contains an error")
	        end
	end,
	ok.
	
get_answer(Message,Answers) ->
   [_|Answer] = 
     lists:reverse(io:get_line(Message)),
   AtomAnswer = list_to_atom(lists:reverse(Answer)),
   case lists:member(AtomAnswer,Answers) of
        true -> AtomAnswer;
        false -> get_answer(Message,Answers)
   end.

ask_question_dependeces(Deps) ->
	{StringDeps,DictDeps} = string_dependences(Deps,1),
	Message = 
		"Related variables:\n" ++ StringDeps ++ "What value is wrong? ",
	Answer = get_answer(Message,[list_to_atom(integer_to_list(Opt)) || {Opt,_} <-  DictDeps]),
	IntAnswer = list_to_integer(atom_to_list(Answer)),
	hd([V || {Opt,V} <-  DictDeps, Opt =:= IntAnswer ]).

string_dependences([{Var,{Value,V}}|Tail],Opt) -> 
	{STail,DictTail} = string_dependences(Tail,Opt + 1),
	SVar = 
		"\t" ++ integer_to_list(Opt) ++ ".- " 
	  	++ atom_to_list(Var) ++ " = " ++ transform_value(Value) ++ "\n",
	{SVar ++ STail,[{Opt,V}|DictTail]};
string_dependences([],_) ->
	{"",[]}.

 
find_unknown_children(G,Unknown,[V|Vs]) ->
	OutNeighbours = digraph:out_neighbours(G, V),
	OutNeighboursUnknown = OutNeighbours -- (OutNeighbours -- Unknown),
	[V | find_unknown_children(G,Unknown,Vs ++ OutNeighboursUnknown)];
find_unknown_children(_,_,[]) ->
	[].
	 
 
print_buggy_node(G,NotCorrectVertex,Message) ->
	{NotCorrectVertex,InfoError} = 
		digraph:vertex(G,NotCorrectVertex),
	io:format("\n\n~s:\n~s\n",[Message,transform_label(InfoError)]).%,
	%print_clause(G,NotCorrectVertex,Clause).
   

	
get_ordinal(1) -> "first";
get_ordinal(2) -> "second";
get_ordinal(3) -> "third";
get_ordinal(4) -> "fourth";
get_ordinal(5) -> "fifth";
get_ordinal(6) -> "sixth";
get_ordinal(7) -> "seventh";
get_ordinal(N) ->
	integer_to_list(N)++"th".
	


asking_loop(_,Strategy,[],Correct,NotCorrect,Unknown,State,_) -> 
	{Correct,NotCorrect,Unknown,State,Strategy};
asking_loop(_,Strategy,[-1],_,_,_,_,_) -> {[-1],[-1],[-1],[],Strategy};
asking_loop(G,Strategy,Vertices,Correct,NotCorrect,Unknown,State,PreSelected) ->
	{Selected,NSortedVertices} = 
		case PreSelected of
			-1 ->
				VerticesWithValues = 
				  case Strategy of 
				       top_down ->
							Children = digraph:out_neighbours(G, hd(NotCorrect)),
							SelectableChildren = Children -- (Children -- Vertices), 
							[{V, - length(digraph_utils:reachable([V], G))} 
							  || V <- SelectableChildren];
				       divide_query ->
							 [{V,begin
							         Reach = digraph_utils:reachable([V], G),
							         TotalReach = length(Reach) - (1 + length(Reach -- Vertices)),
							         Rest = (length(Vertices) - 1) - TotalReach,
							         abs(TotalReach - Rest)
							     end} || V <- Vertices]
				  end,				
				SortedVertices = lists:keysort(2,VerticesWithValues),
				Selected_ = element(1,hd(SortedVertices)),
				NSortedVertices_ = [V || {V,_} <- tl(SortedVertices)],
				{Selected_,NSortedVertices_};
			_ ->
				{PreSelected,Vertices--[PreSelected]}
		end,
	YesAnswer = %begin
	             % EqualToSeleceted = 
	             %    [V || V <- Vertices, begin {V,{L1,_}} = digraph:vertex(G,V),
	             %                               {Selected,{L2,_}} = digraph:vertex(G,Selected),
	             %                               L1 =:= L2
	             %                         end],
	             {NSortedVertices -- digraph_utils:reachable([Selected],G),
	             [Selected|Correct],NotCorrect,Unknown,
	             [{Vertices,Correct,NotCorrect,Unknown,PreSelected}|State],Strategy,-1},
	            %end, 
	Answer = ask_question(G,Selected),
	{NVertices,NCorrect,NNotCorrect,NUnknown,NState,NStrategy,NPreSelected} = 
	   case Answer of
	        y -> YesAnswer;
	        i ->
	        	{Selected,InfoSelected} = digraph:vertex(G,Selected),
	        	{_,_,DepsSelected} = InfoSelected,
	        	%io:format("DepsSelected: ~p\n", [DepsSelected]),
	        	case DepsSelected of 
	        		[] -> YesAnswer;
	        		[{_,{_,NextQuestion}}] ->
	        			{NSortedVertices -- digraph_utils:reachable([Selected],G),
			             [Selected|Correct],NotCorrect,Unknown,
			             [{Vertices,Correct,NotCorrect,Unknown,PreSelected}|State],Strategy,NextQuestion};
	        		_ -> 
	        			NextQuestion = ask_question_dependeces(DepsSelected),
	        			%Podria passar que estaguera entre els correct, notcorret o unknown?
	        			{NSortedVertices -- digraph_utils:reachable([Selected],G),
			             [Selected|Correct],NotCorrect,Unknown,
			             [{Vertices,Correct,NotCorrect,Unknown,PreSelected}|State],Strategy,NextQuestion}
	        	end;
	        n -> {digraph_utils:reachable([Selected],G)
	              -- ([Selected|NotCorrect] ++ Correct ++ Unknown),
	              Correct,[Selected|NotCorrect],Unknown,
	              [{Vertices,Correct,NotCorrect,Unknown,PreSelected}|State],Strategy,-1};
	        d -> %Hacer memoization?
	             {NSortedVertices -- [Selected],
	              Correct,NotCorrect,[Selected|Unknown],
	              [{Vertices,Correct,NotCorrect,Unknown,PreSelected}|State],Strategy,-1};
	        u -> case State of
	                  [] ->
	                     io:format("Nothing to undo\n"),
	                     {Vertices,Correct,NotCorrect,Unknown,State,Strategy,PreSelected};
	                  [{PVertices,PCorrect,PNotCorrect,PUnknown,PPreSelected}|PState] ->
	                     {PVertices,PCorrect,PNotCorrect,PUnknown,PState,Strategy,PPreSelected}
	             end;
	        s -> case get_answer("Select a strategy (Didide & Query or "
	                  ++"Top Down): [d/t] ",[d,t]) of
	                  t -> 
	                     {Vertices,Correct,NotCorrect,Unknown,State,top_down,PreSelected};
	                  d -> 
	                     {Vertices,Correct,NotCorrect,Unknown,State,divide_query,PreSelected}
	             end;
	        a -> {[-1],Correct,NotCorrect,Unknown,State,Strategy,-1};
	        _ -> {Vertices,Correct,NotCorrect,Unknown,State,Strategy,PreSelected}
	   end, 
	asking_loop(G,NStrategy,NVertices,NCorrect,NNotCorrect,NUnknown,NState,NPreSelected).
	
%EN preguntes dobles tindre en conter el undo	
ask_question(G,V)->
	Options = "? [y/n/d/i/s/u/a]: ",
	{V,Info} = digraph:vertex(G,V),
	Question = build_question(Info),
	io:format("~s",[Question]),
	[_|Answer]=lists:reverse(io:get_line(Options)),
	AtomAnswer = list_to_atom(lists:reverse(Answer)),
	case Info of 
		{case_if,{{_,Type},_,_,Value,_},_} ->
			case AtomAnswer of 
				y ->
					Question2 = build_question({case_if,{Type,Value}}),
					io:format("~s",[Question2]),
					[_|Answer2]=lists:reverse(io:get_line(Options)),
					AtomAnswer2 = list_to_atom(lists:reverse(Answer2)),
					case AtomAnswer2 of
						u  ->
							ask_question(G,V);
						_ ->
							AtomAnswer2
					end;
				_ ->
					AtomAnswer
			end;
		_ ->
			AtomAnswer
	end.

build_question({case_if,{Type,Value}}) ->
	"The final value of the " ++ Type 
	++ " expression is " ++ transform_value(Value);
build_question({case_if,{{ACase,Type},ArgValue,ClauseNumber,_,_},Deps}) ->
	Label1 = 
		case Deps of 
			[] ->
				"";
			_ ->
				" the context " ++ get_context(Deps) ++ "\n"
		end,
	Label2 = 
		case ArgValue of 
			[] -> 
				"";
			_ ->
				case Label1 of 
					"" -> "";
					_ -> "and "
				end 
				++ "the " ++ Type ++ " argument value " 
				++ transform_value(ArgValue) ++ ".\n"
		end,
	Label0 = 
		case Label1 ++ Label2 of 
			"" -> "";
			_ -> "Given"
		end,
	Label3 = "The " ++ Type ++ " expression\n" 
		++ transform_abstract(ACase) ++"\nenters in the " 
		++ get_ordinal(ClauseNumber) ++ " clause",
	Label0 ++ Label1 ++ Label2 ++ Label3;
build_question(Info) ->
	Label = transform_label(Info),
	{_,_,Deps} = Info,
	case Deps of 
		[] ->
			io_lib:format("~s",[Label]);
		_ ->
			Context = get_context(Deps),
			io_lib:format("~s\nContext: ~s",[Label,Context])
	end.
	
transform_label({'let',{VarName,Value,_},_}) -> 
	atom_to_list(VarName) ++ " = " ++ transform_value(Value);
transform_label({'let_multiple',{InfoVars,_},_}) -> 
	get_context(InfoVars);
% transform_label({case_if,{{ACase,Type},ArgValue,ClauseNumber,FinalValue,AFinalExpr},_}) ->
% 	Type ++ " expression:\n" ++ transform_value(ACase) ++
%      "\nenters in the " ++ get_ordinal(ClauseNumber) 
%      ++ " clause.\nCase argument value: " ++ transform_value(ArgValue)
%      ++ "\nFinal case value: " ++ transform_value(FinalValue);
transform_label({case_if,{{_,_},_,_,FinalValue,AFinalExpr},_}) ->
	%"The " ++ Type ++ " expression:\n" ++ transform_value(ACase) ++ "\n" ++
     final_expression_message(FinalValue,AFinalExpr);
transform_label({case_if_failed,{{ACase,Type},ArgValue,FinalValue},_}) ->
	"The " ++ Type ++ " expression:\n" ++ transform_abstract(ACase)++
     "\ndoes not enter in any clause."
     ++ "\nCase argument value: " ++ transform_value(ArgValue)
     ++ "\nFinal case value: " ++ transform_value(FinalValue);
transform_label({case_if_clause,{{ACase,Type}, ArgValue, ClauseNumber,PatGuard,SuccFail,Bindings}, _}) ->
	"The " ++ Type ++ " expression:\n" ++ transform_abstract(only_one_case_clause(ACase,ClauseNumber))
	++ "\n" ++ 
	case PatGuard of
		'pattern' ->
			"matching with " ;
		_ ->
			atom_to_list(PatGuard) ++ " of " 
	end
	++ get_ordinal(ClauseNumber) 
	++ " clause " ++ atom_to_list(SuccFail) ++ "\n" ++ Type ++ " argument value :"
	++ transform_value(ArgValue) ++
	case Bindings of 
		[] -> 
			"";
		_ ->
			"\nBindings: " ++ get_context(Bindings)
	end;
transform_label({fun_clause,{FunDef,ClauseNumber,PatGuard,SuccFail},[]}) ->
	"Function:\n" ++ transform_abstract(only_one_fun_clause(FunDef,ClauseNumber))
    ++ "\n" ++ atom_to_list(PatGuard) ++ " of " ++ get_ordinal(ClauseNumber) 
	++ " clause " ++ atom_to_list(SuccFail);
transform_label({'root',{_,FinalValue,AFinalExpr},_}) -> 
	final_expression_message(FinalValue,AFinalExpr).




% transform_value(AFun = {'fun',_,_}) ->
% 	erl_prettypr:format(AFun);
transform_value(Value) ->
	try erl_syntax:type(Value) of 
		_ ->
			erl_prettypr:format(Value)
	catch
		_:_ ->
			lists:flatten(io_lib:format("~p",[Value]))
	end.

transform_abstract(Abstract) ->
	erl_prettypr:format(Abstract).

final_expression_message(FinalValue,AFinalExpr) ->
	"The value " ++ transform_value(FinalValue) ++ " of the final expression " ++
    case AFinalExpr of 
     	[] -> "";
     	[AFinalExpr_|_] -> 
     		transform_abstract(AFinalExpr_) ++ " (Line " 
     			++ integer_to_list(element(2,AFinalExpr_)) ++ ")"
    end ++ " is not correct.".


get_context([]) -> "";
get_context(Deps) ->
	"[" ++ get_context(Deps,[]) ++ "]".

get_context([Entry|Deps],Acc) ->
	{VarName,Value} = 
		case Entry of 
			{VarName_,{Value_,_}} -> 
				{VarName_,Value_};
			{VarName_,Value_} ->
				{VarName_,Value_}
		end,
	VarValue =
		atom_to_list(VarName) ++ " = " ++ transform_value(Value),
	case Deps of 
		[] -> 
			Acc ++ VarValue;
		_ -> 
			get_context(Deps, Acc ++ VarValue ++ ", " )
	end.

only_one_case_clause(ACase,ClauseNumber) ->
	case erl_syntax:type(ACase) of 
		case_expr ->
			Clauses = erl_syntax:case_expr_clauses(ACase),
			Clause = lists:nth(ClauseNumber,Clauses),
			erl_syntax:revert(erl_syntax:case_expr(erl_syntax:case_expr_argument(ACase),[Clause]));
		if_expr ->
			Clauses = erl_syntax:if_expr_clauses(ACase),
			Clause = lists:nth(ClauseNumber,Clauses),
			erl_syntax:revert(erl_syntax:if_expr([Clause]));
		try_expr ->
			Clauses = erl_syntax:try_expr_clauses(ACase),
			Clause = lists:nth(ClauseNumber,Clauses),
			erl_syntax:revert(erl_syntax:try_expr(
				erl_syntax:try_expr_body(ACase),
				[Clause],
				erl_syntax:try_expr_handlers(ACase),
				erl_syntax:try_expr_after(ACase)))
	end.

only_one_fun_clause(AFun,ClauseNumber) ->
	Clauses = erl_syntax:function_clauses(AFun),
	Clause = lists:nth(ClauseNumber,Clauses),
	erl_syntax:revert(erl_syntax:function(erl_syntax:function_name(AFun),[Clause])).
	
% analyze_tokens([]) -> {ok,[]};
% analyze_tokens([H|T]) -> 
% 	case string:to_integer(H) of
% 	     {Int,[]} when Int >= 32, Int =< 126 ->  
% 	     	case analyze_tokens(T) of
% 	     	     {ok,List} -> {ok,[Int|List]};
% 	     	     error -> error
% 	     	end;
% 	     _ -> error
% 	end.
	
		  
%%------------------------------------------------------------------------------
%% @doc Created a DOT file and a PDF file containing the tree in the graph 'G'. 
%%      Creates the file 'Name'.dot containing the description of the digraph 
%%      'G' using the plain text graph description language DOT 
%%      ([http://en.wikipedia.org/wiki/DOT_language]). It also generates a visual 
%%      PDF version of the graph 'G' using the generated DOT file and using the
%%      'dot' command. If this program is not installed in the system the PDF 
%%      will not be created but the function will not throw any exception.
%% @end
%%------------------------------------------------------------------------------
-spec dot_graph_file( G :: digraph(), Name :: string() ) -> string().	   
dot_graph_file(G,Name)->
	file:write_file(Name++".dot", list_to_binary("digraph PDG {\n"++dot_graph(G)++"}")),
	os:cmd("dot -Tpdf "++ Name ++".dot > "++ Name ++".pdf").	
	
dot_graph(G)->
	Vertices = [digraph:vertex(G,V)||V <- digraph:vertices(G)],
	Edges = [{V1,V2}||V1 <- digraph:vertices(G),V2 <- digraph:out_neighbours(G, V1)],
	lists:flatten(lists:map(fun dot_vertex/1,Vertices))++
	lists:flatten(lists:map(fun dot_edge/1,Edges)).
	
	   
dot_vertex({V,L}) ->
	integer_to_list(V)++" "++"[shape=ellipse, label=\""
	++integer_to_list(V)++" .- " 
	++ change_new_lines(lists:flatten(build_question(L))) ++ "\"];\n".

dot_edge({V1,V2}) -> 
	integer_to_list(V1)++" -> "++integer_to_list(V2)
	++" [color=black, penwidth=3];\n".	
	
change_new_lines([10|Chars]) ->
	[$\\,$l|change_new_lines(Chars)];
change_new_lines([$"|Chars]) ->
	[$\\,$"|change_new_lines(Chars)];
change_new_lines([Other|Chars]) ->
	[Other|change_new_lines(Chars)];
change_new_lines([]) ->
	[].
