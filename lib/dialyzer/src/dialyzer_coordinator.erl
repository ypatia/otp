%% -*- erlang-indent-level: 2 -*-
%%-----------------------------------------------------------------------

-module(dialyzer_coordinator).

-export([coordinate/3,
	 coordinate/4,
	 coordinate/5,
	 make_global_st/4,
	 delete_global_st/2]).

-include("dialyzer.hrl").

%---------------------------------------------------------------------

-define(MAX_CONCURRENT, erlang:system_info(schedulers)).

%---------------------------------------------------------------------

%% -type parent() :: 'none' | pid().

%% -record(st, {callgraph      :: dialyzer_callgraph:callgraph(),
%% 	     codeserver     :: dialyzer_codeserver:codeserver(),
%% 	     no_warn_unused :: set(),
%% 	     parent = none  :: parent(),
%% 	     plt            :: dialyzer_plt:plt()}).

%%--------------------------------------------------------------------

%% -spec coordinate(dialyzer_callgraph:callgraph(), pid(), find) -> 

coordinate(Callgraph, Parent, find) ->
  %% io:format("COORDINATOR : ~p \n",[self()]),
  %% {T1, _} = statistics(wall_clock),
  Fast = dialyzer_callgraph:get_fast_plt(Callgraph),
  %% io:format("Fast = ~p",[Fast]),
  Digraph = dialyzer_callgraph:get_digraph2(Callgraph),
  CondensedDigraph = digraph_utils:condensation(Digraph),
  ServerPid = self(),
  Edges = [digraph:edge(CondensedDigraph, E) || E <- digraph:edges(CondensedDigraph)],
  SelfEdges = [E || {E, V, V, _} <- Edges],
  true = digraph:del_edges(CondensedDigraph, SelfEdges),
  ReadyList = dialyzer_callgraph:digraph_leaves(CondensedDigraph),
  %% {ok, Port} = percept_profile:start("results.dat",[procs]),
  CoordinatorPid =
    spawn(fun () ->
	      find_succ_typings_in_parallel(Parent, CondensedDigraph, 
					    ReadyList, Fast, ServerPid)
	  end),
  %% {T2, _} = statistics(wall_clock),
  %% dialyzer_succ_typings:report_elapsed_time(T1,T2,"Coordinate"),
  process_server([], CondensedDigraph, Fast, CoordinatorPid, find).

coordinate(ModuleDigraph, Callgraph, Parent, refine) ->
  %% io:format("COORDINATOR : ~p \n",[self()]),
  %% {T1, _} = statistics(wall_clock),
  ServerPid = self(),
  ReadyList = dialyzer_callgraph:digraph_leaves(ModuleDigraph),
  %%  io:format("ReadyList = ~p \n ", [ReadyList]),
  %%  io:format("Num Of Vertices = ~p\n",[digraph:no_vertices(ModuleDigraph)]),
  CoordinatorPid =
    spawn(fun () ->
	      refine_succ_typings_in_parallel(Parent, ModuleDigraph, Callgraph,
					      ReadyList, ServerPid)
	  end),
  %% {T2, _} = statistics(wall_clock),
  %% dialyzer_succ_typings:report_elapsed_time(T1,T2,"Coordinate"),
  process_server([], ModuleDigraph, CoordinatorPid, refine).


coordinate(Modules, State, BehavioursChk, CWarns, warnings) ->
  ServerPid = self(),
  _Pids = [spawn(fun() ->
		     dialyzer_succ_typings:get_warnings_from_module_parallel(M, State, 
								    BehavioursChk, 
								    ServerPid)
		 end) || M <- Modules],
  Warns = [receive {warnings, Warnings} -> Warnings end || _M <- Modules],
  lists:flatten(CWarns++Warns).


process_server(NotFixpoint, CondensedDigraph, Fast, CoordinatorPid, find) ->
  receive
    {results, SCC, SuccTypes, PltContracts, NewNotFixPoint1} ->
      %% {results, SCC, NewNotFixPoint1} ->
      %% io:format("received message of size ~p of which ~p words are for types an ~p for contract\n", [erts_debug:flat_size(M), erts_debug:flat_size(SuccTypes), erts_debug:flat_size(PltContracts)]),
      %% {results, SCC} ->
      %%   io:format( " irthe to minima apo analyze scc : ~p \n", [SCC]),
      %% [{SCC, {SuccTypes, PltContracts, NewNotFixPoint1}}] = 
      %% ets:lookup(results, SCC), 
      NewNotFixpoint2 = ordsets:union(NewNotFixPoint1, NotFixpoint),
      %% io:format("NewNotFixpoint2 = ~p\n",[NewNotFixpoint2]),
      Parents = get_parents(SCC, CondensedDigraph),
      dialyzer_succ_typings:insert_into_plt(SuccTypes, none, true),
      true = dialyzer_plt:insert_contract_list(none, PltContracts, true),
      case Parents of
	[] ->
	  ok;
	_->
	  CoordinatorPid ! Parents
      end,
      true = digraph:del_vertex(CondensedDigraph, SCC),
      case digraph:no_vertices(CondensedDigraph) =:= 0 of
	true ->
	  CoordinatorPid ! stop,
	  %%  ok = percept_profile:stop(),
	  case dialyzer_succ_typings:check_fixpoint(NewNotFixpoint2, none, Fast, true) of
	    false -> {not_fixpoint, NewNotFixpoint2};
	    true ->  {fixpoint}
	  end;
	false ->
	  process_server(NewNotFixpoint2, CondensedDigraph, Fast, CoordinatorPid, find)
      end
  end.

process_server(NotFixpoint, ModuleDigraph, CoordinatorPid, refine) ->
  receive
    {true, M, FixpointFromScc} ->
      ok;
    {false, M, DictFixpoint, FixpointFromScc} ->
      dialyzer_succ_typings:insert_into_plt(DictFixpoint, none, true)
  end,     
  NewFixpoint = ordsets:union(NotFixpoint, FixpointFromScc),
  Parents = get_parents(M, ModuleDigraph),
  case Parents of
    [] ->
      ok;
    _->
%%      io:format("Exw goneis : ~p\n",[length(M)]),
      CoordinatorPid ! Parents
  end,
  true = digraph:del_vertex(ModuleDigraph, M),
  case digraph:no_vertices(ModuleDigraph) =:= 0 of
    true ->
      %% io:format("Mas teleiwsan oi nodes!!\n"),
      CoordinatorPid ! stop,
      case NewFixpoint =:= [] of
	false -> {not_fixpoint, NewFixpoint};
	true ->  {fixpoint}
      end;
    false ->
      process_server(NewFixpoint, ModuleDigraph, CoordinatorPid, refine)		
  end.    

find_succ_typings_in_parallel(Parent, CondensedDigraph, ReadyList, Fast, ServerPid) ->
  case digraph:no_vertices(CondensedDigraph) =:= 0 of
    true ->
      %%    io:format ( "\nTypesig done"),
      receive stop ->
	  exit(normal)
      end;
    false ->
      %% io:format("Number of processes to be spawned: ~p\n", [length(ReadyList)]),
      _Pids = [spawn(fun() ->
			 dialyzer_succ_typings:analyze_scc_parallel(SCC, ServerPid, Fast)
		     end) || SCC <- ReadyList],
      %% io:format("To mikos twn PIDS: ~p, alive: ~p\n", [length(_Pids), length(processes())]),
      [update_info(SCC, Parent, "Typesig analysis for SCC:") || SCC <- ReadyList],
      receive NewReadyList -> ok end,
      find_succ_typings_in_parallel(Parent, CondensedDigraph, NewReadyList,
				    Fast, ServerPid)	    
  end.


refine_succ_typings_in_parallel(Parent, ModuleDigraph, Callgraph, 
				ReadyList, ServerPid) ->
  case digraph:no_vertices(ModuleDigraph) =:= 0 of
    true ->
      %%    io:format ( "\nTypesig done"),
      receive stop ->
	  exit(normal)
      end;
    false ->
  %%     io:format("Number of processes to be spawned: ~p\n", [length(ReadyList)]),
%%       [io:format("SCC has ~p Modules\n",[length(Scc)])|| Scc <- ReadyList],
      _Pids = [spawn(fun() ->
			 case SCC of 
			   [M] -> dialyzer_succ_typings:refine_one_module_parallel(M, Callgraph, ServerPid);
			   [_|_] -> dialyzer_succ_typings:refine_one_scc_parallel(SCC, Callgraph, ServerPid)
			 end 
		     end) || SCC <- ReadyList],
      %% io:format("To mikos twn PIDS: ~p, alive: ~p\n", [length(_Pids), length(processes())]),
      [update_info(SCC, Parent, "Dataflow of one SCC:") || SCC <- ReadyList],
      receive NewReadyList -> ok end,
      refine_succ_typings_in_parallel(Parent, ModuleDigraph, Callgraph, NewReadyList, ServerPid)	    
  end.



update_info(SCC, Parent, Mode) ->
  Msg = io_lib:format("~s ~w\n", [Mode, dialyzer_succ_typings:format_scc(SCC)]),
  %%  io:format("MESSAGE : ~p \n",[Msg]),
  %% ?debug("~s", [Msg]),
  dialyzer_succ_typings:send_log(Parent, Msg).

get_parents(Node, Digraph) ->
  Vertices = digraph:in_neighbours(Digraph , Node),
  [V || V <- Vertices, digraph:out_degree(Digraph , V) =:= 1].

make_global_st(Callgraph, Codeserver, Plt, Parallel) ->
  case Parallel of 
    true ->
      codeserver1 = ets:new(codeserver1,[protected, named_table]),
      true = ets:insert(codeserver1, [{table_pid, dialyzer_codeserver:get_table_pid(Codeserver)},
				      {next_core_label,  dialyzer_codeserver:get_next_core_label(Codeserver)}]),
      Records = [{{records, Mod}, Record} || 
		  {Mod, Record} <- dict:to_list(dialyzer_codeserver:get_records(Codeserver))],
      Contracts = [{{contracts, Mod}, Contract} || 
		    {Mod, Contract} <- dict:to_list(dialyzer_codeserver:get_contracts(Codeserver))],
      true = ets:insert(codeserver1, Records ++ Contracts),
      exported_types = ets:new(exported_types,[protected, named_table]),
      true = ets:insert(exported_types, {exp_types, dialyzer_codeserver:get_exported_types(Codeserver)}),
      callgraph1 = ets:new(callgraph1,[protected, named_table]),
      true = ets:insert(callgraph1, 
			[{selfrec, dialyzer_callgraph:get_self_rec(Callgraph)},
			 {esc, dialyzer_callgraph:get_escaping(Callgraph)}]),
      RecVarMaps = [{{rec_var_map, Label}, RecVarMap} || 
		     {Label, RecVarMap} <- dict:to_list(dialyzer_callgraph:get_rec_var_map(Callgraph))],
      RevNameMaps = [{{rev_name_map, MFA}, RevNameMap} || 
		      {MFA, RevNameMap} <- dict:to_list(dialyzer_callgraph:get_rev_name_map(Callgraph))],
      NameMaps = [{{name_map, Label}, NameMap} ||  
		   {Label, NameMap} <- dict:to_list(dialyzer_callgraph:get_name_map(Callgraph))],
      Calls = [{{calls, Label}, Calls} ||  
		{Label, Calls} <- dict:to_list(dialyzer_callgraph:get_calls(Callgraph))],
      true = ets:insert(callgraph1, RecVarMaps ++ RevNameMaps ++ NameMaps ++ Calls),
      plt1 = ets:new(plt1,[public, named_table]), 
      Infos =  [{{info, MFA}, Info} ||  
		 {MFA, Info} <- dict:to_list(dialyzer_plt:get_info(Plt))],
      PltContracts = [{{contracts, MFA}, Contract} ||  
		       {MFA, Contract} <- dict:to_list(dialyzer_plt:get_contracts(Plt))],
      true = ets:insert(plt1, Infos ++ PltContracts),
      old_plt = ets:new(old_plt,[public, named_table]), 
      Infos2 =  [{{info, MFA}, Info} ||  
		  {MFA, Info} <- dict:to_list(dialyzer_plt:get_info(Plt))],
      PltContracts2 = [{{contracts, MFA}, Contract} ||  
			{MFA, Contract} <- dict:to_list(dialyzer_plt:get_contracts(Plt))],
      ets:insert(old_plt, Infos2 ++ PltContracts2);
    false ->
      true
  end.

delete_global_st(Plt, Parallel)->
  case Parallel of
    true ->
      Contracts1 = ets:select(plt1,[{{{contracts,'$1'},'$2'},[],[{{'$1','$2'}}]}]),
      Contracts = dict:from_list(Contracts1),
      Info1 = ets:select(plt1,[{{{info,'$1'},'$2'},[],[{{'$1','$2'}}]}]),
      Info = dict:from_list(Info1),
      Plt1 = dialyzer_plt:set_contracts(Plt, Contracts),
      Plt2 = dialyzer_plt:set_info(Plt1, Info),
      ets:delete(codeserver1),
      ets:delete(callgraph1),
      ets:delete(plt1),
      ets:delete(old_plt),
      ets:delete(exported_types),
      Plt2;
    false ->
      Plt
  end.

