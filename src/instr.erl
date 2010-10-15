%%%----------------------------------------------------------------------
%%% File        : instr.erl
%%% Authors     : Alkis Gotovos <el3ctrologos@hotmail.com>
%%%               Maria Christakis <christakismaria@gmail.com>
%%% Description : Instrumenter
%%% Created     : 16 May 2010
%%%
%%% @doc: Instrumenter
%%% @end
%%%----------------------------------------------------------------------

-module(instr).
-export([delete_and_purge/1, instrument_and_load/1]).

-include("gen.hrl").

%%%----------------------------------------------------------------------
%%% Debug
%%%----------------------------------------------------------------------

%%-define(PRINT, true).
-ifdef(PRINT).
-define(debug(S_), io:put_chars(erl_prettypr:format(S_))).
-else.
-define(debug(S_), ok).
-endif.

%%%----------------------------------------------------------------------
%%% Definitions
%%%----------------------------------------------------------------------

-define(INCLUDE_DIR, filename:absname("include")).

%% Instrumented auto-imported functions of 'erlang' module.
-define(INSTR_ERLANG_NO_MOD,
	[demonitor, halt, link, monitor, process_flag, register, spawn,
	 spawn_link, spawn_monitor, unlink, unregister, whereis]).

%% Instrumented functions called as erlang:FUNCTION.
-define(INSTR_ERLANG,
	[send, yield] ++ ?INSTR_ERLANG_NO_MOD).

%%%----------------------------------------------------------------------
%%% Instrumentation utilities
%%%----------------------------------------------------------------------

%% Delete and purge all modules in Files.
-spec delete_and_purge([file()]) -> 'ok'.

delete_and_purge(Files) ->
    ModsToPurge = [list_to_atom(filename:basename(F, ".erl")) || F <- Files],
    [begin code:delete(M), code:purge(M) end || M <- ModsToPurge],
    ok.

%% @spec instrument_and_load(Files::[file()]) -> 'ok' | 'error'
%% @doc: Instrument, compile and load a list of files.
%%
%% Each file is first validated (i.e. checked whether it will compile
%% successfully). If no errors are encountered, the file gets instrumented,
%% compiled and loaded. If all of these actions are successfull, the function
%% returns `ok', otherwise `error' is returned. No `.beam' files are produced.
-spec instrument_and_load([file()]) -> 'ok' | 'error'.

instrument_and_load([]) ->
    log:log("No files instrumented~n"),
    ok;
instrument_and_load([File]) ->
    instrument_and_load_one(File);
instrument_and_load([File | Rest]) ->
    case instrument_and_load_one(File) of
	ok -> instrument_and_load(Rest);
	error -> error
    end.

%% Instrument and load a single file.
instrument_and_load_one(File) ->
    %% Compilation of original file without emitting code, just to show
    %% warnings or stop if an error is found, before instrumenting it.
    log:log("Validating file ~p...~n", [File]),
    PreOptions = [strong_validation, verbose, return, {i, ?INCLUDE_DIR}],
    case compile:file(File, PreOptions) of
	{ok, Module, Warnings} ->
	    %% Log warning messages.
	    log_warning_list(Warnings),
	    %% A table for holding used variable names.
	    ets:new(?NT_USED, [named_table, private]),
	    %% Instrument given source file.
	    log:log("Instrumenting file ~p...~n", [File]),
	    case instrument(File) of
		{ok, NewForms} ->
		    %% Delete `used` table.
		    ets:delete(?NT_USED),
		    %% Compile instrumented code.
		    %% TODO: More compile options?
		    log:log("Compiling instrumented code...~n"),
		    CompOptions = [binary],
		    case compile:forms(NewForms, CompOptions) of
			{ok, Module, Binary} ->
			    log:log("Loading module `~p`...~n", [Module]),
			    case code:load_binary(Module, File, Binary) of
				{module, Module} ->
				    ok;
				{error, Error} ->
				    log:log("error~n~p~n", [Error]),
				    error
			    end;
			error ->
			    log:log("error~n"),
			    error
		    end;
		{error, Error} ->
		    log:log("error: ~p~n", [Error]),
		    %% Delete `used` table.
		    ets:delete(?NT_USED),
		    error
	    end;
	{error, Errors, Warnings} ->
	    log_error_list(Errors),
	    log_warning_list(Warnings),
	    log:log("error~n"),
	    error
    end.

instrument(File) ->
    %% TODO: For now using the default and the test directory include path.
    %%       In the future we have to provide a means for an externally
    %%       defined include path (like the erlc -I flag).
    case epp:parse_file(File, [?INCLUDE_DIR, filename:dirname(File)], []) of
	{ok, OldForms} ->
	    Tree = erl_recomment:recomment_forms(OldForms, []),
	    MapFun = fun(T) -> instrument_toplevel(T) end,
	    Transformed = erl_syntax_lib:map_subtrees(MapFun, Tree),
	    Abstract = erl_syntax:revert(Transformed),
            ?debug(Abstract),
	    NewForms = erl_syntax:form_list_elements(Abstract),
	    {ok, NewForms};
	{error, Error} -> {error, Error}
    end.

%% Instrument a "top-level" element.
%% Of the "top-level" elements, i.e. functions, specs, etc., only functions are
%% transformed, so leave everything else as is.
instrument_toplevel(Tree) ->
    case erl_syntax:type(Tree) of
	function -> instrument_function(Tree);
	_Other -> Tree
    end.

%% Instrument a function.
instrument_function(Tree) ->
    %% Delete previous entry in `used` table (if any).
    ets:delete_all_objects(?NT_USED),
    %% A set of all variables used in the function.
    Used = erl_syntax_lib:variables(Tree),
    %% Insert the used set into `used` table.
    ets:insert(?NT_USED, {used, Used}),
    instrument_subtrees(Tree).

%% Instrument all subtrees of Tree.
instrument_subtrees(Tree) ->
    MapFun = fun(T) -> instrument_term(T) end,
    erl_syntax_lib:map_subtrees(MapFun, Tree).

%% Instrument a term.
instrument_term(Tree) ->
    case erl_syntax:type(Tree) of
	application ->
	    NewTree = instrument_subtrees(Tree),
	    case get_mfa(NewTree) of
		no_instr -> NewTree;
		Mfa -> instrument_application(Mfa)
	    end;
	infix_expr ->
	    Operator = erl_syntax:infix_expr_operator(Tree),
	    case erl_syntax:operator_name(Operator) of
		'!' -> instrument_send(instrument_subtrees(Tree));
		_Other -> instrument_subtrees(Tree)
	    end;
	receive_expr -> instrument_receive(instrument_subtrees(Tree));
	underscore -> new_underscore_variable();
	_Other -> instrument_subtrees(Tree)
    end.

%% Return {ModuleAtom, FunctionAtom, ArgTree} for a function that is going
%% to be instrumented or 'no_instr' otherwise.
get_mfa(Tree) ->
    Qualifier = erl_syntax:application_operator(Tree),
    case erl_syntax:type(Qualifier) of
	atom ->
	    Function = erl_syntax:atom_value(Qualifier),
	    case lists:member(Function, ?INSTR_ERLANG_NO_MOD) of
		true ->
                    ArgTree = erl_syntax:application_arguments(Tree),
                    {erlang, Function, ArgTree};
		false -> no_instr
	    end;
	module_qualifier ->
	    ModTree = erl_syntax:module_qualifier_argument(Qualifier),
	    FunTree = erl_syntax:module_qualifier_body(Qualifier),
	    case erl_syntax:type(ModTree) =:= atom andalso
		erl_syntax:type(FunTree) =:= atom of
		true ->
		    Module = erl_syntax:atom_value(ModTree),
		    case Module of
			erlang ->
                            Function = erl_syntax:atom_value(FunTree),
			    case lists:member(Function, ?INSTR_ERLANG) of
				true ->
				    ArgTree =
					erl_syntax:application_arguments(Tree),
				    {Module, Function, ArgTree};
				false -> no_instr
			    end;
			_Other -> no_instr
		    end;
		false -> no_instr
	    end;
	_Other -> no_instr
    end.

%% Instrument an application (function call).
instrument_application({erlang, Fun, ArgTree}) ->
    ModTree = erl_syntax:atom(sched),
    FunTree = erl_syntax:atom(list_to_atom("rep_" ++ atom_to_list(Fun))),
    erl_syntax:application(ModTree, FunTree, ArgTree).

%% Instrument a receive expression.
%% -----------------------------------------------------------------------------
%% receive
%%   Patterns -> Actions
%% end
%%
%% is transformed into
%%
%% sched:rep_receive(Fun),
%% receive
%%   NewPatterns -> NewActions
%% end
%%
%% where Fun = fun(Aux) ->
%%               receive
%%                 NewPatterns -> continue
%%                 [_Fresh -> block]
%%               after 0 ->
%%                 Aux()
%%               end
%%             end
%%
%% The additional _Fresh -> block pattern is only added, if there is no
%% catch-all pattern among the original receive patterns.
%%
%% Pattern -> NewPattern maps are divided into the following categories:
%%
%%   - Patterns consisting of size-3 tuples, i.e. `{X, Y, Z}' are kept as
%%     they are and additionally a pattern `{Fresh, {X, Y, Z}}' is added.
%%     That way possible `{'EXIT', Pid, Reason}' messages are caught
%%     if the receiver has trap_exit set to true.
%%
%%   - Same as above for size-5 tuples, to catch possible 'DOWN' messages.
%%
%%   - Same as above for catch-all patterns, i.e. `Var' or `_' patterns.
%%
%%   - All other patterns `Pattern' are transformed into {Fresh, Pattern}.
%%
%% `Action' is normally transformed into
%% `sched:rep_receive_notify(Fresh, Pattern), Action'.
%% In the case of size-3, size-5 and catch-all patterns, the patterns that
%% are duplicated as they were originally, will have a NewAction of
%% `sched:rep_receive_notify(Pattern), Action'.
%% -----------------------------------------------------------------------------
%% receive
%%   Patterns -> Actions
%% after N -> AfterAction
%%
%% is transformed into
%%
%% receive
%%   NewPatterns -> NewActions
%% after 0 -> NewAfterAction
%%
%% Pattens and Actions are mapped into NewPatterns and NewActions as described
%% previously for the case of a `receive' expression with no `after' clause.
%% AfterAction is transformed into `sched:rep_after_notify(), AfterAction'.
%% -----------------------------------------------------------------------------
%% receive
%% after N -> AfterActions
%%
%% is transformed into
%%
%% AfterActions
%%
%% That is, the `receive' expression and the delay are dropped off completely.
%% -----------------------------------------------------------------------------
instrument_receive(Tree) ->
    %% Get old receive expression's clauses.
    OldClauses = erl_syntax:receive_expr_clauses(Tree),
    case OldClauses of
        %% Keep only the action of any `receive after' construct
        %% without patterns.
        [] ->
            Action = erl_syntax:receive_expr_action(Tree),
            erl_syntax:block_expr(Action);
        _Other ->
	    NewClauses = transform_receive_clauses(OldClauses),
            %% Create new receive expression adding the `after 0` part.
            Timeout = erl_syntax:integer(0),
            case erl_syntax:receive_expr_timeout(Tree) of
                %% Instrument `receive` without `after` part.
                none ->
		    %% Create fun(X) -> case X of ... end end.
                    FunVar = new_variable(),
		    CaseClauses = transform_receive_case(NewClauses),
		    Case = erl_syntax:case_expr(FunVar, CaseClauses),
		    FunClause = erl_syntax:clause([FunVar], [], [Case]),
                    FunExpr = erl_syntax:fun_expr([FunClause]),
                    %% Create sched:rep_receive(fun(X) -> ...).
		    Module = erl_syntax:atom(sched),
		    Function = erl_syntax:atom(rep_receive),
                    RepReceive = erl_syntax:application(Module, Function,
							[FunExpr]),
		    %% Crete new receive expression.
                    NewReceive = erl_syntax:receive_expr(NewClauses),
		    %% Result is begin rep_receive(...), NewReceive end.
                    erl_syntax:block_expr([RepReceive, NewReceive]);
                %% Instrument `receive` with `after` part.
                _Any ->
                    [Action] = erl_syntax:receive_expr_action(Tree),
		    RepMod = erl_syntax:atom(sched),
		    RepFun = erl_syntax:atom(rep_after_notify),
		    RepApp = erl_syntax:application(RepMod, RepFun, []),
		    NewAction = [RepApp, Action],
                    erl_syntax:receive_expr(NewClauses, Timeout, NewAction)
            end
    end.

transform_receive_case(Clauses) ->
    Fun = fun(Clause, HasCatchall) ->
		  [Pattern] = erl_syntax:clause_patterns(Clause),
		  NewBody = erl_syntax:atom(continue),
		  NewHasCatchall = HasCatchall orelse
		      erl_syntax:type(Pattern) =:= variable,
		  {erl_syntax:clause([Pattern], [], [NewBody]), NewHasCatchall}
	  end,
    case lists:mapfoldl(Fun, false, Clauses) of
	{NewClauses, false} ->
	    Pattern = new_underscore_variable(),
	    Body = erl_syntax:atom(block),
	    CatchallClause = erl_syntax:clause([Pattern], [], [Body]),
	    NewClauses ++ [CatchallClause];
	{NewClauses, true} -> NewClauses
    end.

transform_receive_clauses(Clauses) ->
    Fold = fun(Old, Acc) ->
		   case transform_receive_clause(Old) of
		       [One] -> [One|Acc];
		       [One, Two] -> [One, Two|Acc]
		   end
	   end,
    lists:foldr(Fold, [], Clauses).

%% Transform a Pattern -> Action clause, according to its Pattern.
transform_receive_clause(Clause) ->
    [Pattern] = erl_syntax:clause_patterns(Clause),
    Fnormal = fun(P) -> [transform_receive_clause_regular(P)] end,
    Fspecial = fun(P) -> [transform_receive_clause_regular(P),
     			  transform_receive_clause_special(P)]
    	       end,
    case erl_syntax:type(Pattern) of
	tuple ->
	    case erl_syntax:tuple_size(Pattern) of
		3 -> Fspecial(Clause);
		5 -> Fspecial(Clause);
		_OtherSize -> Fnormal(Clause)
	    end;
	variable -> Fspecial(Clause);
	_OtherType -> Fnormal(Clause)
    end.    

%% Tranform a clause
%%   Pattern -> Action
%% into
%%   {Fresh, Pattern} -> sched:rep_receive_notify(Fresh, Pattern), Action
transform_receive_clause_regular(Clause) ->
    [OldPattern] = erl_syntax:clause_patterns(Clause),
    OldGuard = erl_syntax:clause_guard(Clause),
    OldBody = erl_syntax:clause_body(Clause),
    PidVar = new_variable(),
    NewPattern = [erl_syntax:tuple([PidVar, OldPattern])],
    Module = erl_syntax:atom(sched),
    Function = erl_syntax:atom(rep_receive_notify),
    Arguments = [PidVar, OldPattern],
    Notify = erl_syntax:application(Module, Function, Arguments),
    NewBody = [Notify|OldBody],
    erl_syntax:clause(NewPattern, OldGuard, NewBody).

%% Transform a clause
%%   Pattern -> Action
%% into
%%   Pattern -> sched:rep_receive_notify(Pattern), Action
transform_receive_clause_special(Clause) ->
    [OldPattern] = erl_syntax:clause_patterns(Clause),
    OldGuard = erl_syntax:clause_guard(Clause),
    OldBody = erl_syntax:clause_body(Clause),
    Module = erl_syntax:atom(sched),
    Function = erl_syntax:atom(rep_receive_notify),
    Arguments = [OldPattern],
    Notify = erl_syntax:application(Module, Function, Arguments),
    NewBody = [Notify|OldBody],
    erl_syntax:clause([OldPattern], OldGuard, NewBody).

%% Instrument a Pid ! Msg expression.
%% Pid ! Msg is transformed into rep:send(Pid, Msg).
instrument_send(Tree) ->
    Module = erl_syntax:atom(sched),
    Function = erl_syntax:atom(rep_send),
    Dest = erl_syntax:infix_expr_left(Tree),
    Msg = erl_syntax:infix_expr_right(Tree),
    Arguments = [Dest, Msg],
    erl_syntax:application(Module, Function, Arguments).

%%%----------------------------------------------------------------------
%%% Helper functions
%%%----------------------------------------------------------------------

new_variable() ->
    [{used, Used}] = ets:lookup(?NT_USED, used),
    Fresh = erl_syntax_lib:new_variable_name(Used),
    ets:insert(?NT_USED, {used, sets:add_element(Fresh, Used)}),
    erl_syntax:variable(Fresh).

new_underscore_variable() ->
    [{used, Used}] = ets:lookup(?NT_USED, used),
    new_underscore_variable(Used).

new_underscore_variable(Used) ->
    Fresh1 = erl_syntax_lib:new_variable_name(Used),
    String = "_" ++ atom_to_list(Fresh1),
    Fresh2 = list_to_atom(String),
    case is_fresh(Fresh2, Used) of
        true ->
            ets:insert(?NT_USED, {used, sets:add_element(Fresh2, Used)}),
            erl_syntax:variable(Fresh2);
        false ->
            new_underscore_variable(Used)
    end.

is_fresh(Atom, Set) ->
    not sets:is_element(Atom, Set).

%%%----------------------------------------------------------------------
%%% Logging
%%%----------------------------------------------------------------------

%% Log a list of errors, as returned by compile:file/2.
log_error_list(List) ->
    log_list(List, "").

%% Log a list of warnings, as returned by compile:file/2.
log_warning_list(List) ->
    log_list(List, "Warning:").

%% Log a list of error or warning descriptors, as returned by compile:file/2.
log_list(List, Pre) ->
    LogFun = fun(String) -> log:log(String) end,
    [LogFun(io_lib:format("~s:~p: ~s ", [File, Line, Pre]) ++
                Mod:format_error(Descr) ++ "\n") || {File, Info} <- List,
                                                    {Line, Mod, Descr} <- Info].
