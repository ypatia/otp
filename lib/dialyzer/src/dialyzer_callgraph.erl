%% -*- erlang-indent-level: 2 -*-
%%-----------------------------------------------------------------------
%% %CopyrightBegin%
%%
%% Copyright Ericsson AB 2006-2010. All Rights Reserved.
%%
%% The contents of this file are subject to the Erlang Public License,
%% Version 1.1, (the "License"); you may not use this file except in
%% compliance with the License. You should have received a copy of the
%% Erlang Public License along with this software. If not, it can be
%% retrieved online at http://www.erlang.org/.
%%
%% Software distributed under the License is distributed on an "AS IS"
%% basis, WITHOUT WARRANTY OF ANY KIND, either express or implied. See
%% the License for the specific language governing rights and limitations
%% under the License.
%%
%% %CopyrightEnd%
%%

%%%-------------------------------------------------------------------
%%% File    : dialyzer_callgraph.erl
%%% Author  : Tobias Lindahl <tobiasl@it.uu.se>
%%% Description :
%%%
%%% Created : 30 Mar 2005 by Tobias Lindahl <tobiasl@it.uu.se>
%%%-------------------------------------------------------------------
-module(dialyzer_callgraph).

-export([add_edges/2,
	 all_nodes/1,
	 changed/3,
	 delete/1,
	 digraph_leaves/1,
	 finalize/1,
	 get_calls/1,
	 get_changed_funs/1,
	 get_escaping/1,
	 get_name_map/1,
	 get_rev_name_map/1,
	 get_rec_var_map/1,
	 get_self_rec/1,
	 is_escaping/2,
	 is_escaping/3,
	 is_self_rec/2,
	 is_self_rec/3,
	 non_local_calls/1,
	 lookup_rec_var/2,
	 lookup_rec_var/3,
	 lookup_call_site/2,
	 lookup_call_site/3,
	 lookup_label/2,
	 lookup_label/3,
	 lookup_name/2,
	 lookup_name/3,
	 modules/1,
	 module_deps/1,
	 %% module_postorder/1,
	 module_postorder_from_funs/2,
	 need_analysis/3,
	 new/0,
	 in_neighbours/2,
	 in_neighbours/3,
	 renew_race_info/3,
	 reset_from_funs/2,
	 scan_core_tree/2,
	 strip_module_deps/2,
	 shrink/1,
	 take_scc/1,
	 remove_external/1,
	 to_dot/2,
	 to_ps/3]).

%% Data structure interfaces.
-export([cleanup/2, get_digraph/1,  get_digraph2/1, 
         get_race_detection/1, put_digraph/2, put_race_detection/2,
         put_behaviour_api_calls/2, get_behaviour_api_calls/1, 
	 put_diff_mods/2, put_fast_plt/2, get_fast_plt/1]).

-export_type([callgraph/0, scc/0]).

-include("dialyzer.hrl").

%%----------------------------------------------------------------------

-type mfa_or_funlbl() :: label() | mfa().
-type scc()	      :: [mfa_or_funlbl()].
-type mfa_calls()     :: [{mfa_or_funlbl(), mfa_or_funlbl()}].

%%-----------------------------------------------------------------------------
%% A callgraph is a directed graph where the nodes are functions and a
%% call between two functions is an edge from the caller to the callee.
%%
%% calls	-  A mapping from call site (and apply site) labels
%%		   to the possible functions that can be called.
%% digraph	-  A digraph representing the callgraph.
%%		   Nodes are represented as MFAs or labels.
%% esc		-  A set of all escaping functions as reported by dialyzer_dep.
%% postorder	-  A list of strongly connected components of the callgraph
%%		   sorted in a topological bottom-up order.
%%		   This is produced by calling finalize/1.
%% name_map	-  A mapping from label to MFA.
%% rev_name_map	-  A reverse mapping of the name_map.
%% rec_var_map	-  A dict mapping from letrec bound labels to function names.
%%		   Only for top level functions (from module defs).
%% self_rec	-  A set containing all self recursive functions.
%%		   Note that this contains MFAs for named functions and labels
%%		   whenever applicable.
%%-----------------------------------------------------------------------------

-record(callgraph, {digraph        = digraph:new() :: digraph(),
		    digraph2       = digraph:new() :: digraph(),
                    esc	           = sets:new()    :: set(),
                    name_map	   = dict:new()    :: dict(),
                    rev_name_map   = dict:new()    :: dict(),
                    postorder      = []	           :: [scc()],
                    rec_var_map    = dict:new()    :: dict(),
                    self_rec	   = sets:new()    :: set(),
                    calls          = dict:new()    :: dict(),
                    public_tables  = []            :: [label()],
                    named_tables   = []            :: [string()],
                    race_detection = false         :: boolean(),
		    beh_api_calls  = []            :: [{mfa(), mfa()}],
		    diff_mods      = []            :: [atom()],
		    depends_on     = dict:new()    :: dict(),
		    is_dependent   = dict:new()    :: dict(),
		    changed_funs   = sets:new()    :: set(),
		    fast_plt       = false         :: boolean()}).

%% Exported Types

-type callgraph() :: #callgraph{}.

%%----------------------------------------------------------------------

-spec new() -> callgraph().

new() ->
  #callgraph{}.

-spec get_changed_funs(callgraph()) -> set().  

get_changed_funs(#callgraph{changed_funs = ChangedFuns}) ->
  ChangedFuns.

-spec get_name_map(callgraph()) -> dict().  % set(mfa())

get_name_map(#callgraph{name_map = NameMap}) ->
  NameMap.

-spec get_rev_name_map(callgraph()) -> dict().  % set(mfa())

get_rev_name_map(#callgraph{rev_name_map = RevNameMap}) ->
  RevNameMap.

-spec get_rec_var_map(callgraph()) -> dict().  % set(mfa())

get_rec_var_map(#callgraph{rec_var_map = RecVarMap}) ->
  RecVarMap.

-spec get_calls(callgraph()) -> dict().  % set(mfa())

get_calls(#callgraph{calls = Calls}) ->
  Calls.

-spec get_self_rec(callgraph()) -> set().  % set(mfa())

get_self_rec(#callgraph{self_rec = SelfRec}) ->
  SelfRec.

-spec get_escaping(callgraph()) -> set().  % set(mfa())

get_escaping(#callgraph{esc = Esc}) ->
  Esc.

-spec delete(callgraph()) -> 'true'.

delete(#callgraph{digraph = Digraph}) ->
  digraph_delete(Digraph).

-spec all_nodes(callgraph()) -> [mfa()].

all_nodes(#callgraph{digraph = DG}) ->
  digraph_vertices(DG).

-spec lookup_rec_var(label(), callgraph() | 'undefined', boolean()) -> 
			'error' | {'ok', mfa()}.

lookup_rec_var(Label, _Callgraph, true) when is_integer(Label) ->
  case ets:lookup(?Cg_RecVarMap, Label) of
    [] -> error;
    [{_, MFA}] -> {ok, MFA}
  end;
lookup_rec_var(Label, Callgraph, false) -> 
  lookup_rec_var(Label, Callgraph).

-spec lookup_rec_var(label(), callgraph()) -> 'error' | {'ok', mfa()}.

lookup_rec_var(Label, #callgraph{rec_var_map = RecVarMap})
  when is_integer(Label) ->
  dict:find(Label, RecVarMap). 

-spec lookup_call_site(label(), callgraph() | 'undefined', boolean()) ->
			  'error' | {'ok', [_]}. % XXX: refine

lookup_call_site(Label, CG, false) ->
  lookup_call_site(Label, CG);
lookup_call_site(Label, _Callgraph, true) when is_integer(Label) ->
  case ets:lookup(?Cg_Calls, Label) of
    [] -> error;
    [{_,List}] -> {ok, List}
  end.

-spec lookup_call_site(label(), callgraph()) -> 'error' | {'ok', [_]}. % XXX: refine

lookup_call_site(Label, #callgraph{calls = Calls})
  when is_integer(Label) ->
  dict:find(Label, Calls).

-spec lookup_name(label(), callgraph() | 'undefined', boolean()) ->
		     'error' | {'ok', mfa()}.

lookup_name(Label, _Callgraph, true) when is_integer(Label) ->
  case ets:lookup(?Cg_NameMap,  Label) of
    [] -> error;
    [{_, MFA}] -> {ok, MFA}
  end;
lookup_name(Label, Callgraph, false) ->
  lookup_name(Label, Callgraph).

-spec lookup_name(label(), callgraph()) -> 'error' | {'ok', mfa()}.

lookup_name(Label, #callgraph{name_map = NameMap})
  when is_integer(Label) ->
  dict:find(Label, NameMap).

-spec lookup_label(mfa_or_funlbl(), callgraph()|'undefined', boolean()) -> 
		      'error' | {'ok', integer()}.

lookup_label({_,_,_} = MFA, _Callgraph, true) ->
  case ets:lookup(?Cg_RevNameMap, MFA) of
    [] -> error;
    [{_, Label}] -> {ok, Label}
  end;
lookup_label(Label, _Callgraph, true) when is_integer(Label) ->
  {ok, Label};
lookup_label(MfaOrLabel, Callgraph, false) ->
  lookup_label(MfaOrLabel, Callgraph).

-spec lookup_label(mfa_or_funlbl(), callgraph()) -> 'error' | {'ok', integer()}.

lookup_label({_,_,_} = MFA, #callgraph{rev_name_map = RevNameMap}) ->
  dict:find(MFA, RevNameMap);
lookup_label(Label, #callgraph{}) when is_integer(Label) ->
  {ok, Label}.

-spec in_neighbours(mfa_or_funlbl(), callgraph(), boolean()) ->
		       'none' | [mfa_or_funlbl(),...].

in_neighbours(Label, #callgraph{digraph = Digraph} = Callgraph, Parallel) 
  when is_integer(Label) ->
  Name = case lookup_name(Label, Callgraph, Parallel) of
	   {ok, Val} -> Val;
	   error -> Label
	 end,
  digraph_in_neighbours(Name, Digraph);
in_neighbours({_, _, _} = MFA, #callgraph{digraph = Digraph}, _Parallel) ->
  digraph_in_neighbours(MFA, Digraph).

-spec in_neighbours(mfa_or_funlbl(), callgraph()) -> 'none' | [mfa_or_funlbl(),...].

in_neighbours(Label, #callgraph{digraph = Digraph, name_map = NameMap})
  when is_integer(Label) ->
  Name = case dict:find(Label, NameMap) of
	   {ok, Val} -> Val;
	   error -> Label
	 end,
  digraph_in_neighbours(Name, Digraph);
in_neighbours({_, _, _} = MFA, #callgraph{digraph = Digraph}) ->
  digraph_in_neighbours(MFA, Digraph).

-spec is_self_rec(mfa_or_funlbl(), callgraph() | 'undefined', boolean()) -> 
		     boolean().

is_self_rec(MfaOrLabel, CG, false) ->
  is_self_rec(MfaOrLabel, CG);
is_self_rec(MfaOrLabel, _CG, true) ->
  [{_ , SelfRecs}] = ets:lookup(?Callgraph, selfrec),
  sets:is_element(MfaOrLabel, SelfRecs).

-spec is_self_rec(mfa_or_funlbl(), callgraph()) -> boolean().

is_self_rec(MfaOrLabel, #callgraph{self_rec = SelfRecs}) ->
  sets:is_element(MfaOrLabel, SelfRecs).

-spec is_escaping(label(), callgraph() | 'undefined', boolean()) -> boolean().

is_escaping(Label, Callgraph, Parallel) when is_integer(Label) ->
  case Parallel of
    true -> 
      [{_ , Esc}] = ets:lookup(?Callgraph, esc);
    false ->
      Esc = Callgraph#callgraph.esc
  end,
  sets:is_element(Label, Esc).  

-spec is_escaping(label(), callgraph()) -> boolean().

is_escaping(Label, #callgraph{esc = Esc}) when is_integer(Label) ->
  sets:is_element(Label, Esc).

-type callgraph_edge() :: {mfa_or_funlbl(),mfa_or_funlbl()}.
-spec add_edges([callgraph_edge()], callgraph()) -> callgraph().

add_edges([], CG) ->
  CG;
add_edges(Edges, #callgraph{digraph = Digraph} = CG) ->
  CG#callgraph{digraph = digraph_add_edges(Edges, Digraph)}.

-spec add_edges([callgraph_edge()], [mfa_or_funlbl()], callgraph()) -> callgraph().

add_edges(Edges, MFAs, #callgraph{digraph = DG} = CG) ->
  DG1 = digraph_confirm_vertices(MFAs, DG),
  add_edges(Edges, CG#callgraph{digraph = DG1}).

-spec take_scc(callgraph()) -> 'none' | {'ok', scc(), callgraph()}.

take_scc(#callgraph{postorder = [SCC|SCCs]} = CG) ->
  {ok, SCC, CG#callgraph{postorder = SCCs}};
take_scc(#callgraph{postorder = []}) ->
  none.

-spec remove_external(callgraph()) -> {callgraph(), [tuple()]}.

remove_external(#callgraph{digraph = DG} = CG) ->
  {NewDG, External} = digraph_remove_external(DG),
  {CG#callgraph{digraph = NewDG}, External}.

-spec non_local_calls(callgraph()) -> mfa_calls().

non_local_calls(#callgraph{digraph = DG}) ->
  Edges = digraph_edges(DG),
  find_non_local_calls(Edges, sets:new()).

-spec find_non_local_calls([{mfa_or_funlbl(), mfa_or_funlbl()}], set()) -> mfa_calls().

find_non_local_calls([{{M,_,_}, {M,_,_}}|Left], Set) ->
  find_non_local_calls(Left, Set);
find_non_local_calls([{{M1,_,_}, {M2,_,_}} = Edge|Left], Set) when M1 =/= M2 ->
  find_non_local_calls(Left, sets:add_element(Edge, Set));
find_non_local_calls([{{_,_,_}, Label}|Left], Set) when is_integer(Label) ->
  find_non_local_calls(Left, Set);
find_non_local_calls([{Label, {_,_,_}}|Left], Set) when is_integer(Label) ->
  find_non_local_calls(Left, Set);
find_non_local_calls([{Label1, Label2}|Left], Set) when is_integer(Label1),
							is_integer(Label2) ->
  find_non_local_calls(Left, Set);
find_non_local_calls([], Set) ->
  sets:to_list(Set).

-spec renew_race_info(callgraph(), [label()], [string()]) ->
			 callgraph().

renew_race_info(CG, PublicTables, NamedTables) ->
  CG#callgraph{public_tables = PublicTables,
               named_tables = NamedTables}.

%%----------------------------------------------------------------------
%% Handling of modules & SCCs
%%----------------------------------------------------------------------

-spec modules(callgraph()) -> [module()].

modules(#callgraph{digraph = DG}) ->
  ordsets:from_list([M || {M,_F,_A} <- digraph_vertices(DG)]).

-spec module_postorder(callgraph()) -> {[[module()]], digraph()}.

module_postorder(#callgraph{digraph = DG}) ->
  Edges = digraph_edges(DG),
  Nodes = ordsets:from_list([M || {M,_F,_A} <- digraph_vertices(DG)]),
  MDG = digraph:new(),
  MDG1 = digraph_confirm_vertices(Nodes, MDG),
  MDG2 = create_module_digraph(Edges, MDG1),
  MDG3 = digraph_utils:condensation(MDG2),
  PostOrder = digraph_utils:postorder(MDG3),
  PostOrder1 = sort_sccs_internally(PostOrder, MDG2),
  digraph:delete(MDG2),
  Edges2 = [digraph:edge(MDG3, E) || E <- digraph:edges(MDG3)],
  SelfEdges = [E || {E, V, V, _} <- Edges2],
  true = digraph:del_edges(MDG3, SelfEdges),
  {PostOrder1, MDG3}.

%% The module deps of a module are modules that depend on the module
-spec module_deps(callgraph()) -> dict().

module_deps(#callgraph{digraph = DG}) ->
  Edges = digraph_edges(DG),
  Nodes = ordsets:from_list([M || {M,_F,_A} <- digraph_vertices(DG)]),
  MDG = digraph:new(),
  MDG1 = digraph_confirm_vertices(Nodes, MDG),
  MDG2 = create_module_digraph(Edges, MDG1),
  Deps = [{N, ordsets:from_list(digraph:in_neighbours(MDG2, N))}
	  || N <- Nodes],
  digraph_delete(MDG2),
  dict:from_list(Deps).

-spec strip_module_deps(dict(), set()) -> dict().

strip_module_deps(ModDeps, StripSet) ->
  FilterFun1 = fun(Val) -> not sets:is_element(Val, StripSet) end,
  MapFun = fun(_Key, ValSet) -> ordsets:filter(FilterFun1, ValSet) end,
  ModDeps1 = dict:map(MapFun, ModDeps),
  FilterFun2 = fun(_Key, ValSet) -> ValSet =/= [] end,
  dict:filter(FilterFun2, ModDeps1).

sort_sccs_internally(PO, MDG) ->
  sort_sccs_internally(PO, MDG, []).

sort_sccs_internally([SCC|SCCs], MDG, Acc) ->
  case SCC of
    [_, _, _ | _] ->    % length(SCC) >= 3
      TmpDG = digraph_utils:subgraph(MDG, SCC),
      NewSCC = digraph_utils:postorder(TmpDG),
      digraph_delete(TmpDG),
      sort_sccs_internally(SCCs, MDG, [NewSCC|Acc]);
    _ ->
      sort_sccs_internally(SCCs, MDG, [SCC|Acc])
  end;
sort_sccs_internally([], _MDG, Acc) ->
  lists:reverse(Acc).

create_module_digraph([{{M, _, _}, {M, _, _}}|Left], MDG) ->
  create_module_digraph(Left, MDG);
create_module_digraph([{{M1, _, _}, {M2, _, _}}|Left], MDG) ->
  create_module_digraph(Left, digraph_add_edge(M1, M2, MDG));
create_module_digraph([{_, _}|Left], MDG) ->
  create_module_digraph(Left, MDG);
create_module_digraph([], MDG) ->
  MDG.

-spec finalize(callgraph()) -> callgraph().

finalize(#callgraph{fast_plt = FastPlt} = CG) ->
  case FastPlt of
    true  -> fast_finalize(CG);
    false -> slow_finalize(CG)
  end.

fast_finalize(#callgraph{digraph = DG, diff_mods = DiffMods} = CG) ->
  DG1 = digraph_utils:condensation(DG),
  ChangedFuns = dependencies(DG1, DiffMods),
  PostOrder = digraph_finalize(DG1, DiffMods),
  CG#callgraph{postorder = PostOrder,
	       changed_funs = ChangedFuns,
	       digraph2 = DG}.

slow_finalize(#callgraph{digraph = DG, diff_mods = DiffMods} = CG) ->
  DG1 = digraph_utils:condensation(DG),
  PostOrder = digraph_finalize(DG1, DiffMods),
  CG#callgraph{postorder = PostOrder, digraph2 = DG}.

-spec reset_from_funs([mfa_or_funlbl()], callgraph()) -> callgraph().

reset_from_funs(Funs, #callgraph{fast_plt = FastPlt} = CG) ->
  case FastPlt of
    true  -> fast_reset_from_funs(Funs, CG);
    false -> slow_reset_from_funs(Funs, CG)
  end.

fast_reset_from_funs(Funs, #callgraph{digraph = DG, diff_mods = DiffMods} = CG) ->
  SubGraph = digraph_reaching_subgraph(Funs, DG),
  SG1 = digraph_utils:condensation(SubGraph),
  _ChangedFuns = dependencies(SG1, DiffMods),
  PostOrder = digraph_finalize(SG1, DiffMods),
  CG#callgraph{postorder    = PostOrder,
	       digraph2 = SubGraph}.

slow_reset_from_funs(Funs, #callgraph{digraph = DG} = CG) ->
  SubGraph = digraph_reaching_subgraph(Funs, DG),
  Postorder = slow_digraph_finalize(SubGraph),
  CG#callgraph{postorder = Postorder, digraph2 = SubGraph}.

-spec module_postorder_from_funs([mfa_or_funlbl()], callgraph()) ->
				    {[[module()]], digraph()}.

module_postorder_from_funs(Funs, #callgraph{digraph = DG} = CG) ->
  SubGraph = digraph_reaching_subgraph(Funs, DG),
  {PO, DG2} = module_postorder(CG#callgraph{digraph = SubGraph}),
  digraph_delete(SubGraph),
  {PO, DG2}.

%%----------------------------------------------------------------------
%% Core code
%%----------------------------------------------------------------------

%% The core tree must be labeled as by cerl_trees:label/1 (or /2).
%% The set of labels in the tree must be disjoint from the set of
%% labels already occuring in the callgraph.

-spec scan_core_tree(cerl:c_module(), callgraph()) -> callgraph().

scan_core_tree(Tree, #callgraph{calls = OldCalls,
				esc = OldEsc,
				name_map = OldNameMap,
				rec_var_map = OldRecVarMap,
				rev_name_map = OldRevNameMap,
				self_rec = OldSelfRec} = CG) ->
  %% Build name map and recursion variable maps.
  {NewNameMap, NewRevNameMap, NewRecVarMap} =
    build_maps(Tree, OldRecVarMap, OldNameMap, OldRevNameMap),

  %% First find the module-local dependencies.
  {Deps0, EscapingFuns, Calls} = dialyzer_dep:analyze(Tree),
  NewCalls = dict:merge(fun(_Key, Val, Val) -> Val end, OldCalls, Calls),
  NewEsc = sets:union(sets:from_list(EscapingFuns), OldEsc),
  LabelEdges = get_edges_from_deps(Deps0),

  %% Find the self recursive functions. Named functions get both the
  %% key and their name for convenience.
  SelfRecs0 = lists:foldl(fun({Key, Key}, Acc) ->
			      case dict:find(Key, NewNameMap) of
				error      -> [Key|Acc];
				{ok, Name} -> [Key, Name|Acc]
			      end;
			     (_, Acc) -> Acc
			  end, [], LabelEdges),
  SelfRecs = sets:union(sets:from_list(SelfRecs0), OldSelfRec),

  NamedEdges1 = name_edges(LabelEdges, NewNameMap),

  %% We need to scan for inter-module calls since these are not tracked
  %% by dialyzer_dep. Note that the caller is always recorded as the
  %% top level function. This is OK since the included functions are
  %% stored as scc with the parent.
  NamedEdges2 = scan_core_funs(Tree),

  %% Confirm all nodes in the tree.
  Names1 = lists:append([[X, Y] || {X, Y} <- NamedEdges1]),
  Names2 = ordsets:from_list(Names1),

  %% Get rid of the 'top' function from nodes and edges.
  Names3 = ordsets:del_element(top, Names2),
  NewNamedEdges2 =
    [E || {From, To} = E <- NamedEdges2, From =/= top, To =/= top],
  NewNamedEdges1 =
    [E || {From, To} = E <- NamedEdges1, From =/= top, To =/= top],
  NamedEdges3 = NewNamedEdges1 ++ NewNamedEdges2,
  CG1 = add_edges(NamedEdges3, Names3, CG),
  CG1#callgraph{calls = NewCalls,
                esc = NewEsc,
                name_map = NewNameMap,
                rec_var_map = NewRecVarMap,
                rev_name_map = NewRevNameMap,
                self_rec = SelfRecs}.

build_maps(Tree, RecVarMap, NameMap, RevNameMap) ->
  %% We only care about the named (top level) functions. The anonymous
  %% functions will be analysed together with their parents.
  Defs = cerl:module_defs(Tree),
  Mod = cerl:atom_val(cerl:module_name(Tree)),
  lists:foldl(fun({Var, Function}, {AccNameMap, AccRevNameMap, AccRecVarMap}) ->
		  FunName = cerl:fname_id(Var),
		  Arity = cerl:fname_arity(Var),
		  MFA = {Mod, FunName, Arity},
		  {dict:store(get_label(Function), MFA, AccNameMap),
		   dict:store(MFA, get_label(Function), AccRevNameMap),
		   dict:store(get_label(Var), MFA, AccRecVarMap)}
	      end, {NameMap, RevNameMap, RecVarMap}, Defs).

get_edges_from_deps(Deps) ->
  %% Convert the dependencies as produced by dialyzer_dep to a list of
  %% edges. Also, remove 'external' since we are not interested in
  %% this information.
  Edges = dict:fold(fun(external, _Set, Acc) -> Acc;
		       (Caller, Set, Acc)    ->
			[[{Caller, Callee} || Callee <- Set,
					      Callee =/= external]|Acc]
		    end, [], Deps),
  lists:flatten(Edges).

name_edges(Edges, NameMap) ->
  %% If a label is present in the name map it is renamed. Otherwise
  %% keep the label as the identity.
  MapFun = fun(X) ->
	       case dict:find(X, NameMap) of
		 error -> X;
		 {ok, MFA} -> MFA
	       end
	   end,
  name_edges(Edges, MapFun, NameMap, []).

name_edges([{From, To}|Left], MapFun, NameMap, Acc) ->
  NewFrom = MapFun(From),
  NewTo = MapFun(To),
  name_edges(Left, MapFun, NameMap, [{NewFrom, NewTo}|Acc]);
name_edges([], _MapFun, _NameMap, Acc) ->
  Acc.

scan_core_funs(Tree) ->
  Defs = cerl:module_defs(Tree),
  Mod = cerl:atom_val(cerl:module_name(Tree)),
  DeepEdges = lists:foldl(fun({Var, Function}, Edges) ->
			      FunName = cerl:fname_id(Var),
			      Arity = cerl:fname_arity(Var),
			      MFA = {Mod, FunName, Arity},
			      [scan_one_core_fun(Function, MFA)|Edges]
			  end, [], Defs),
  lists:flatten(DeepEdges).

scan_one_core_fun(TopTree, FunName) ->
  FoldFun = fun(Tree, Acc) ->
		case cerl:type(Tree) of
		  call ->
		    CalleeM = cerl:call_module(Tree),
		    CalleeF = cerl:call_name(Tree),
		    A = length(cerl:call_args(Tree)),
		    case (cerl:is_c_atom(CalleeM) andalso
			  cerl:is_c_atom(CalleeF)) of
		      true ->
			M = cerl:atom_val(CalleeM),
			F = cerl:atom_val(CalleeF),
			case erl_bif_types:is_known(M, F, A) of
			  true -> Acc;
			  false -> [{FunName, {M, F, A}}|Acc]
			end;
		      false ->
			%% We cannot handle run-time bindings
			Acc
		    end;
		  _ ->
		    %% Nothing that can introduce new edges in the callgraph.
		    Acc
		end
	    end,
  cerl_trees:fold(FoldFun, [], TopTree).

get_label(T) ->
  case cerl:get_ann(T) of
    [{label, L} | _] when is_integer(L) -> L;
    _ -> erlang:error({missing_label, T})
  end.

%%----------------------------------------------------------------------
%% Digraph
%%----------------------------------------------------------------------

digraph_add_edges([{From, To}|Left], DG) ->
  digraph_add_edges(Left, digraph_add_edge(From, To, DG));
digraph_add_edges([], DG) ->
  DG.

digraph_add_edge(From, To, DG) ->
  case digraph:vertex(DG, From) of
    false -> digraph:add_vertex(DG, From);
    {From, _} -> ok
  end,
  case digraph:vertex(DG, To) of
    false -> digraph:add_vertex(DG, To);
    {To, _} -> ok
  end,
  digraph:add_edge(DG, {From, To}, From, To, []),
  DG.

digraph_confirm_vertices([MFA|Left], DG) ->
  digraph:add_vertex(DG, MFA, confirmed),
  digraph_confirm_vertices(Left, DG);
digraph_confirm_vertices([], DG) ->
  DG.

digraph_remove_external(DG) ->
  Vertices = digraph:vertices(DG),
  Unconfirmed = remove_unconfirmed(Vertices, DG),
  {DG, Unconfirmed}.

remove_unconfirmed(Vertexes, DG) ->
  remove_unconfirmed(Vertexes, DG, []).

remove_unconfirmed([V|Left], DG, Unconfirmed) ->
  case digraph:vertex(DG, V) of
    {V, confirmed} -> remove_unconfirmed(Left, DG, Unconfirmed);
    {V, []} -> remove_unconfirmed(Left, DG, [V|Unconfirmed])
  end;
remove_unconfirmed([], DG, Unconfirmed) ->
  BadCalls = lists:append([digraph:in_edges(DG, V) || V <- Unconfirmed]),
  BadCallsSorted = lists:keysort(1, BadCalls),
  digraph:del_vertices(DG, Unconfirmed),
  BadCallsSorted.

digraph_delete(DG) ->
  digraph:delete(DG).

digraph_edges(DG) ->
  digraph:edges(DG).

digraph_vertices(DG) ->
  digraph:vertices(DG).

digraph_in_neighbours(V, DG) ->
  case digraph:in_neighbours(DG, V) of
    [] -> none;
    List -> List
  end.

%% Pick all the independent nodes (leaves) from one module. Then try
%% to stay within the module until no more independent nodes can be
%% chosen. Then pick a new module and so on.
%%
%% Note that an SCC that ranges over more than one module is
%% considered to belong to all modules to make sure that we do not
%% lose any nodes.

digraph_postorder(Digraph, DiffMods) ->
  %% Remove all self-edges for SCCs.
  Edges = [digraph:edge(Digraph, E) || E <- digraph:edges(Digraph)],
  SelfEdges = [E || {E, V, V, _} <- Edges],
  true = digraph:del_edges(Digraph, SelfEdges),
  %% Determine the first module outside of the loop.
  Leaves = digraph_leaves(Digraph),
  case Leaves =:= [] of
    true -> [];
    false ->
      {Module, Taken} = take_sccs_from_fresh_module(Leaves, DiffMods),
      true = digraph:del_vertices(Digraph, Taken),
      digraph_postorder(Digraph, Module, [Taken], DiffMods)
  end.

digraph_postorder(Digraph, LastModule, Acc, DiffMods) ->
  Leaves = digraph_leaves(Digraph),
  case Leaves =:= [] of
    true -> lists:append(lists:reverse(Acc));
    false ->
      case [SCC || SCC <- Leaves, scc_belongs_to_module(SCC, LastModule)] of
	[] ->
	  {NewModule, NewTaken} = take_sccs_from_fresh_module(Leaves, DiffMods),
	  true = digraph:del_vertices(Digraph, NewTaken),
	  digraph_postorder(Digraph, NewModule, [NewTaken|Acc], DiffMods);
	NewTaken ->
	  true = digraph:del_vertices(Digraph, NewTaken),
	  digraph_postorder(Digraph, LastModule, [NewTaken|Acc], DiffMods)
      end
  end.

-spec digraph_leaves(digraph()) -> [term()].

digraph_leaves(Digraph) ->
  [V || V <- digraph:vertices(Digraph), digraph:out_degree(Digraph, V) =:= 0].

take_sccs_from_fresh_module(Leaves, DiffMods) ->
  NewModule =
    case find_leaf_in_diff(Leaves, DiffMods) of
      none   -> find_module(hd(Leaves));
      {ok,H} -> H
    end,
  {NewModule, [SCC || SCC <- Leaves, scc_belongs_to_module(SCC, NewModule)]}.

find_leaf_in_diff(_Leaves, []) ->
  none;
find_leaf_in_diff([Leaf|Leaves], DiffMods) ->
  case [M || {M,_,_} <- Leaf, lists:member(M, DiffMods)] of
    [H|_T] -> {ok, H};
    []     -> find_leaf_in_diff(Leaves, DiffMods)
  end;
find_leaf_in_diff([], _DiffMods) ->
  none.

-spec scc_belongs_to_module(scc(), module()) -> boolean().

scc_belongs_to_module([Label|Left], Module) when is_integer(Label) ->
  scc_belongs_to_module(Left, Module);
scc_belongs_to_module([{M, _, _}|Left], Module) ->
  if M =:= Module -> true;
     true -> scc_belongs_to_module(Left, Module)
  end;
scc_belongs_to_module([], _Module) ->
  false.

-spec find_module(scc()) -> module().

find_module([{M, _, _}|_]) -> M;
find_module([Label|Left]) when is_integer(Label) -> find_module(Left).

digraph_finalize(DG, DiffMods) ->
  digraph_postorder(DG, DiffMods).

slow_digraph_finalize(DG) ->
  DG1 = digraph_utils:condensation(DG),
  Postorder = digraph_postorder(DG1, []),
  Postorder.

digraph_reaching_subgraph(Funs, DG) ->
  Vertices = digraph_utils:reaching(Funs, DG),
  digraph_utils:subgraph(DG, Vertices).

%%----------------------------------------------------------------------
%% Races
%%----------------------------------------------------------------------

-spec cleanup(callgraph(), boolean()) -> callgraph().

cleanup(#callgraph{digraph = Digraph}, true)->
  #callgraph{digraph = Digraph};
cleanup(#callgraph{digraph = Digraph,  
		   name_map = NameMap,                                  
                   rev_name_map = RevNameMap}, false)->                    
  #callgraph{digraph = Digraph,
             name_map = NameMap,                                          
             rev_name_map = RevNameMap}.

-spec get_digraph(callgraph()) -> digraph().

get_digraph(#callgraph{digraph = Digraph}) ->
  Digraph.

-spec get_digraph2(callgraph()) -> digraph().

get_digraph2(#callgraph{digraph2 = Digraph}) ->
  Digraph.

-spec get_race_detection(callgraph()) -> boolean().

get_race_detection(#callgraph{race_detection = RD}) ->
  RD.

-spec put_digraph(digraph(), callgraph()) -> callgraph().

put_digraph(Digraph, Callgraph) ->
  Callgraph#callgraph{digraph = Digraph}.

-spec put_race_detection(boolean(), callgraph()) -> callgraph().

put_race_detection(RaceDetection, Callgraph) ->
  Callgraph#callgraph{race_detection = RaceDetection}.

-spec shrink(callgraph()) -> callgraph().

shrink(#callgraph{digraph = Digraph,                               
		  race_detection = RaceDetection,                        
		  beh_api_calls = BehApiCalls}) ->                    
  #callgraph{digraph = Digraph,                                    
	     race_detection = RaceDetection,                 
	     beh_api_calls = BehApiCalls}.

%%=============================================================================
%% Utilities for 'dot'
%%=============================================================================

-spec to_dot(callgraph(), file:filename()) -> 'ok'.

to_dot(#callgraph{digraph = DG, esc = Esc} = CG, File) ->
  Fun = fun(L) ->
	    case lookup_name(L, CG) of
	      error -> L;
	      {ok, Name} -> Name
	    end
	end,
  Escaping = [{Fun(L), {color, red}}
	      || L <- sets:to_list(Esc), L =/= external],
  Vertices = digraph_edges(DG),
  hipe_dot:translate_list(Vertices, File, "CG", Escaping).

-spec to_ps(callgraph(), file:filename(), string()) -> 'ok'.

to_ps(#callgraph{} = CG, File, Args) ->
  Dot_File = filename:rootname(File) ++ ".dot",
  to_dot(CG, Dot_File),
  Command = io_lib:format("dot -Tps ~s -o ~s ~s", [Args, File, Dot_File]),
  _ = os:cmd(Command),
  ok.

%%-----------------------------------------------------------------------------

-spec put_behaviour_api_calls([{mfa(), mfa()}], callgraph()) -> callgraph().

put_behaviour_api_calls(Calls, Callgraph) ->
  Callgraph#callgraph{beh_api_calls = Calls}.

-spec get_behaviour_api_calls(callgraph()) -> [{mfa(), mfa()}].

get_behaviour_api_calls(Callgraph) ->
  Callgraph#callgraph.beh_api_calls.

%%-------------------------------------------------------------------------------

-spec put_diff_mods([atom()], callgraph()) -> callgraph().

put_diff_mods(DiffMods, Callgraph) ->
  Callgraph#callgraph{diff_mods = DiffMods}.

-spec put_fast_plt(boolean(), callgraph()) -> callgraph().

put_fast_plt(FastPlt, Callgraph) ->
  Callgraph#callgraph{fast_plt = FastPlt}.

-spec get_fast_plt(callgraph()) -> boolean().

get_fast_plt(Callgraph) ->
  Callgraph#callgraph.fast_plt.

%%=============================================================================
%% Utilities for faster plt check
%%=============================================================================

dependencies(DG, DiffMods) ->
  F = digraph:vertices(DG),
  DependsOnList  = [{{depends_on, F1}, digraph:out_neighbours(DG, F1)} || 
		     F1 <- F],
  DependentsList = [{{dependent_of, F1}, digraph:in_neighbours(DG, F1)} || 
		     F1 <- F],
  true = ets:insert(?Dependencies, DependsOnList ++ DependentsList),
  DiffF = [L || L <- F, {M,_,_} <- L, lists:member(M,DiffMods)],
  NeedF = needed_fixpoint(DiffF),
  DifferFuns = lists:foldl(fun sets:add_element/2, sets:new(), DiffF),
  ChangedFuns = lists:foldl(fun sets:add_element/2, DifferFuns, NeedF),
  true = ets:insert(?Changed_Funs, [{R,[]} || R <- sets:to_list(ChangedFuns)]),
  ChangedFuns.

needed_fixpoint(DiffF) ->
  needed_fixpoint(DiffF, sets:new(), 0).

needed_fixpoint(Base, Set, OldSize) ->
  NewBase = lists:append([ets:lookup(?Dependencies, {depends_on, Q}) 
			  || Q <- Base]),
  CleanBase = [V || {_,V} <- NewBase, not sets:is_element(V, Set)],
  NewSet = lists:foldl(fun sets:add_element/2, Set, CleanBase),
  NewSize = sets:size(NewSet),
  case NewSize =:= OldSize of
    true  -> sets:to_list(Set);
    false -> needed_fixpoint(CleanBase, NewSet, NewSize)
  end.

-spec need_analysis(scc(), callgraph() | 'undefined', boolean()) -> boolean().

need_analysis(SCC, _Callgraph, true) ->
  ets:lookup(?Changed_Funs, SCC) =/= [];
need_analysis(SCC, Callgraph, false) ->
  sets:is_element(SCC, Callgraph#callgraph.changed_funs).

-spec changed(scc(), callgraph() | 'undefined', boolean()) -> 
		 callgraph() | 'undefined'.

changed(SCC, Callgraph, false) ->
  DependentsDict = Callgraph#callgraph.is_dependent,
  DependsOnDict = Callgraph#callgraph.depends_on,
  ChangedFuns = Callgraph#callgraph.changed_funs,
  {ok, SCCDependents} = dict:find(SCC,DependentsDict),
  DepDependenciesFun = fun(V,L1) -> [dict:fetch(V, DependsOnDict)|L1] end,
  DepDependencies = lists:foldl(DepDependenciesFun, [], SCCDependents),
  NewChangedFuns =
    lists:foldl(fun sets:add_element/2, ChangedFuns, DepDependencies),
  Callgraph#callgraph{changed_funs = NewChangedFuns};
changed(SCC, Callgraph, true) ->
  [{_, SCCDependents}] = ets:lookup(?Dependencies, {dependent_of, SCC}),
  DepDependenciesFun = fun(V,L1) -> [{_, H}] = ets:lookup(?Dependencies, 
							  {depends_on, V}),
				    [H|L1] 
		       end,
  DepDependencies = lists:foldl(DepDependenciesFun, [], SCCDependents),
  true = ets:insert(?Changed_Funs, [{DD, []} || DD <- DepDependencies]),
  Callgraph.

%%-------------------------------------------------------------------------------
