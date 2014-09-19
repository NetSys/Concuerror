%% -*- erlang-indent-level: 2 -*-

-module(concuerror_scheduler).

%% User interface
-export([run/1, explain_error/1]).

%%------------------------------------------------------------------------------

%%-define(DEBUG, true).
-define(CHECK_ASSERTIONS, true).
-define(EUNIT_NOAUTO, 1).

-include("concuerror.hrl").
-include_lib("eunit/include/eunit.hrl").
%%------------------------------------------------------------------------------

%% -type clock_vector() :: orddict:orddict(). %% orddict(pid(), index()).
-type clock_map()    :: dict:dict(). %% dict(pid(), clock_vector()).

%%------------------------------------------------------------------------------

%% =============================================================================
%% DATA STRUCTURES
%% =============================================================================

-type event_tree() :: [{event(), event_tree()}].

% It's worth explaining what 'trace_state' is within this context
% Basically, for every BIF (jiffie) add a 'trace state' that contains:
%   * All actors seen thus far.
%   * A vector clock associated with each actor stating when it executed.
%   * Events that have just finished executing (Done).
%
% 'Done' might not be a single event, it can also take form of:
% {receive_event, Special = [message_received]}, 
% {message_event, Special = [message_delivered, message_received, 
%                           system_communication, message]}
% 
% I believe the reson for this is to remove unnecessary races 
% between message_receive and message_delivered. Thus message_delivered
% is just ignored.
-record(trace_state, {
          actors      = []         :: [pid() | {channel(), queue:queue()}],
          clock_map   = dict:new() :: clock_map(),
          delay_bound = infinity   :: bound(),
          done        = []         :: [event()],
          index       = 1          :: index(),
          graph_ref   = make_ref() :: reference(),
          sleeping    = []         :: [event()],
          wakeup_tree = []         :: event_tree(),
          freeze      = false      :: boolean()
         }).

-type trace_state() :: #trace_state{}.

-record(scheduler_state, {
          ignore_first_crash = true :: boolean(),
          assume_racing     = true :: boolean(),
          current_graph_ref        :: reference(),
          current_warnings  = []   :: [concuerror_warning_info()],
          delay             = 0    :: non_neg_integer(),
          depth_bound              :: pos_integer(),
          entry_point              :: mfargs(),
          first_process            :: pid(),
          ignore_error      = []   :: [atom()],
          logger                   :: pid(),
          last_scheduled           :: pid(),
          message_info             :: message_info(),
          non_racing_system = []   :: [atom()],
          optimal           = true :: boolean(),
          print_depth              :: pos_integer(),
          processes                :: processes(),
          scheduling = oldest      :: scheduling(),
		  algo = 'dpor'            :: algo(),
          show_races = true        :: boolean(),
          strict_scheduling = false :: boolean(),
          system            = []   :: [pid()],
          timeout                  :: timeout(),
          trace             = []   :: [trace_state()],
          treat_as_normal   = []   :: [atom()]
         }).

%% =============================================================================
%% LOGIC (high level description of the exploration algorithm)
%% =============================================================================

-spec run(options()) -> ok.

run(Options) ->
  process_flag(trap_exit, true),
  case code:get_object_code(erlang) =:= error of
    true ->
      true =
        code:add_pathz(filename:join(code:root_dir(), "erts/preloaded/ebin"));
    false ->
      ok
  end,
  {FirstProcess, System} =
    concuerror_callback:spawn_first_process(Options),
  InitialTrace =
    #trace_state{
       actors = [FirstProcess],
       delay_bound = ?opt(delay_bound, Options)
      },
  InitialState =
    #scheduler_state{
       ignore_first_crash = ?opt(ignore_first_crash, Options),
       assume_racing = ?opt(assume_racing, Options),
       depth_bound = ?opt(depth_bound, Options),
       entry_point = EntryPoint = ?opt(entry_point, Options),
       first_process = FirstProcess,
       ignore_error = ?opt(ignore_error, Options),
       last_scheduled = FirstProcess,
       logger = Logger = ?opt(logger, Options),
       message_info = ets:new(message_info, [private]),
       non_racing_system = ?opt(non_racing_system, Options),
       optimal = ?opt(optimal, Options),
       print_depth = ?opt(print_depth, Options),
       processes = ?opt(processes, Options),
       scheduling = ?opt(scheduling, Options),
	   algo = ?opt(algo, Options),
       show_races = ?opt(show_races, Options),
       strict_scheduling = ?opt(strict_scheduling, Options),
       system = System,
       trace = [InitialTrace],
       treat_as_normal = ?opt(treat_as_normal, Options),
       timeout = Timeout = ?opt(timeout, Options)
      },
  ok = concuerror_callback:start_first_process(FirstProcess, EntryPoint, Timeout),
  concuerror_logger:plan(Logger),
  ?time(Logger, "Exploration start"),
  explore(InitialState).




% Done exploring one configuration (branch).
%
% (a) Run the actor scheduler which runs all actors till completion.
% (b) Try to plan more interleavings.
% (c) Find a starting point from which the trace should be explored. This is
%     done by iterating through the configuration states and truncating it at the
%     first encounter of a wakup tree.
% (d) If no such prefix exists, this means we're done. Nothing more to
%     explore (no wake-up trees present)!
% (e) Otherwise:
%     (e1) instruct the replay scheduler to replay that prefix.
%     (e2) Recursiverlly call explore
explore(State) ->
  UpdatedState = actor_scheduler(State), % (a)
  RacesDetectedState = plan_interleavings(UpdatedState), % (b)
  LogState = log_trace(RacesDetectedState),

  #scheduler_state{trace = Trace} = LogState,
  TracePrefix = find_prefix(Trace, LogState), % (c)
  
  case TracePrefix =:= [] of
    true -> ok; % (d)
    false ->
	  FinalState = reply_scheduler(TracePrefix, State), % (e1)
      explore(FinalState) % (e2)
  end.



actor_scheduler(#scheduler_state{current_warnings = Warnings,
				   depth_bound = Bound,
				   trace = [#trace_state{index = I}|Old]} = State)
      when I =:= Bound + 1->
	
  StateBounds = State#scheduler_state{
  	current_warnings = [{depth_bound, Bound}|Warnings],
  	trace = Old
  },
  
  update_state(StateBounds);


actor_scheduler(State) ->
  #scheduler_state{trace = [CurrentTrace|_]} = State,
  
  #trace_state{
    index = _Index
  } = CurrentTrace,
  
  {Status, UpdatedEvent} = try
	{Event, Actors, ScheduledState} = schedule_actors(State),
	get_next_event(Event, Actors, ScheduledState)
  catch
    exit:Reason -> handle_crash(Reason, State)
  end,

  case Status of
	ok ->   
	  UpdatedState = update_state(UpdatedEvent, State),
      actor_scheduler(UpdatedState);
	none ->
	  update_state(State)
  end.


% (a) Replay that prefix.
% (b) Replay the wakup tree that trigers the race.  
reply_scheduler(TracePrefix, #scheduler_state{logger = Logger} = State) ->

  ?time(Logger, "New interleaving. Replaying..."),
  Message = ["Replaying " ++ integer_to_list(length(TracePrefix)) ++ " events"],
  print_debug(yellow, Message),
  
  NewState = replay_prefix(TracePrefix, State), % (a)
  
  print_debug(yellow, ["Replay done"]),
  ?debug(Logger, "~s~n",["Replay done."]),
  
  PreWUTState = NewState#scheduler_state{trace = TracePrefix},
  
  replay_wakeup_tree(PreWUTState). % (b)


handle_crash(Reason, State) ->
  #scheduler_state{
    current_warnings = Warnings,
    trace = [_CurrentTrace|Old]
  } = State,
  
  FatalCrashState = State#scheduler_state{
    current_warnings = [fatal|Warnings],
    trace = Old
  },
  
  catch log_trace(FatalCrashState),
  exit(Reason).

%% =============================================================================
%% EVENT FUNCTIONS
%% =============================================================================

%% Interesting code.
schedule_actors(#scheduler_state{
				   system = System, 
				   trace = [Last|_]} = State) ->
  
  #trace_state{actors      = Actors,
     		   sleeping    = Sleeping,
     		   wakeup_tree = [] 
  } = Last,
  
  SortedActors = schedule_sort(Actors, State),
  AvailableActors = filter_sleeping(Sleeping, SortedActors),
  % Run through Actors in round robin order. 
  % Allocate an event to hold data about what happened
  Event = #event{label = make_ref()},
  {Event, System ++ AvailableActors, State#scheduler_state{delay = 0}}.


%% get_next_event(Event, Actors, SchedulerState);
%% Call next actor in order.
%% If we have a channel just deliver it.
get_next_event(Event, [{Channel, Queue}|_], SchedulerState) ->
  %% Pending messages can always be sent
  MessageEvent = queue:get(Queue),
  UpdatedEvent = Event#event{actor = Channel, event_info = MessageEvent},
  % This will always be ok, FinalEvent since messages are never blocked.
  get_next_event_backend(UpdatedEvent, SchedulerState); 


% If the first thing is a process then
get_next_event(Event, [P|ActiveProcesses], SchedulerState) ->
  % Try calling process. 
  case get_next_event_backend(Event#event{actor = P}, SchedulerState) of
    % If blocked, try remaining processes.
    retry -> get_next_event(Event, ActiveProcesses, SchedulerState);
    {ok, UpdatedEvent} -> {ok, UpdatedEvent}
  end;


get_next_event(Event, [], _State) ->
  {none, Event}.

update_state(State) ->
  %% Nothing to do, trace is completely explored
  #scheduler_state{
     current_warnings = Warnings,
     logger = Logger,
     trace = [Last|Prev]
    } = State,
  #trace_state{actors = Actors, sleeping = Sleeping} = Last,
  NewWarnings =
    case Sleeping =/= [] of
      true ->
        ?debug(Logger, "Sleep set block:~n ~p~n", [Sleeping]),
        ?unique(Logger, ?lwarning, msg(sleep_set_block), []),
        [sleep_set_block];
      false ->
        case concuerror_callback:collect_deadlock_info(Actors) of
          [] -> Warnings;
          Info ->
            ?debug(Logger, "Deadlock: ~p~n", [[P || {P,_} <- Info]]),
            [{deadlock, Info}|Warnings]
        end
    end,
  State#scheduler_state{current_warnings = NewWarnings, trace = Prev}.



%% Between scheduler and an instrumented process, provides mechanisms to actually
%% execute what the scheduler desires.

% If the next thing is message delivery.
get_next_event_backend(#event{actor = Channel} = Event, State)
  when ?is_channel(Channel) ->
  
  #scheduler_state{timeout = Timeout} = State,
  #event{event_info = MessageEvent} = Event,
  % Make sure no pending messages.
  assert_no_messages(),
  % Deliver message. This involves delivering a message and waiting for an ack. Event
  % is updated according to the ack,
  UpdatedEvent =
    concuerror_callback:deliver_message(Event, MessageEvent, Timeout),
  {ok, UpdatedEvent};


% If the next thing is to get an actor to take a step.
get_next_event_backend(#event{actor = Pid} = Event, State) 
  when is_pid(Pid) ->
  
  #scheduler_state{timeout = Timeout} = State,
  assert_no_messages(),
  % Send actor the event.
  Pid ! Event,
  % Wait for response, can either be retry or {ok, NewEvent} 
  concuerror_callback:wait_actor_reply(Event, Timeout).


reset_event(#event{actor = Actor, event_info = EventInfo}) ->
  ResetEventInfo =
    case ?is_channel(Actor) of
      true -> EventInfo;
      false -> undefined
    end,
  #event{
     actor = Actor,
     event_info = ResetEventInfo,
     label = make_ref()
    }.



% Complexity:
% plan_interleavings                      |
%   |--> split_trace                      | N +
%   |--> assign_happens_before            | N^2 +
%     |--> happens_before_clock           |
%   |--> plan_interleavings_dpor          | N^3
%     |--> plan_interleavings_for_event   | 
%       |--> get_dependent_action         |
%                                         = N^3
%
% High level explanation of the exploration algorithm:
%
% We initially start off with a new configuration. Since this is a new
% configuration, non of the trace states have no clocks assigned, causing
% split_trace to return [0, N], when N is the number of states in the 
% configuration
%
% Next, assign_happens_before for all untimed events in the configuration. This
% basically updates the clock map for those events.
plan_interleavings(#scheduler_state{algo = Algo} = State) 
  	when Algo =:= dpor ->
  
  print_debug(red, ["================ new exploration ================"]),

  #scheduler_state{logger = Logger, trace = RevTrace} = State,
  ?time(Logger, "Assigning happens-before..."),
  % Split into half which has timing information and half which does not.
  {RevEarly, UntimedLate} = split_trace(RevTrace),
  print_debug(blue, ["================ RevEarly0 "
				   ++ integer_to_list(length(RevEarly)) 
				   ++ " | Late "
				   ++ integer_to_list(length(UntimedLate))]),

    
  % Assign happens before to everything. In other words find races.
  Late = assign_happens_before(UntimedLate, RevEarly, State),
  
  %?time(Logger, "Planning more interleavings..."),

  NewRevTrace = plan_interleavings_dpor(
                  lists:reverse(RevEarly, Late), [], State),
  
  State#scheduler_state{trace = NewRevTrace};

% Exceprt from the paper:
%
% "In the actor model, actors have no shared states but only communicate by 
% exchanging messages. Since processing a message in one actor cannot change
% the states of other actors, only the transitions that process the messages
% sent to the same actor are dependent. Hence, when exploring actor systems,
% to reach all local safety violations and deadlocks, it suffices to explore
% different interleavings of processing messages in each actor, i.e., it is
% not necessary to explore interleavings of pro cessing messages across
% different actors."
plan_interleavings(#scheduler_state{algo = Algo} = State) 
  	when Algo =:= transdpor ->
  
  print_debug(red, ["================ new exploration ================"]),

  #scheduler_state{logger = Logger, trace = RevTrace} = State,
  ?time(Logger, "Assigning happens-before..."),
  % Split into half which has timing information and half which does not.
  {RevEarly, UntimedLate} = split_trace(RevTrace),
  
  print_debug(blue, ["================ RevEarly0 "
				   ++ integer_to_list(length(RevEarly)) 
				   ++ " | Late "
				   ++ integer_to_list(length(UntimedLate))]),

    
  % Assign happens before to everything. In other words find races.
  Late = assign_happens_before(UntimedLate, RevEarly, State),
  
  %?time(Logger, "Planning more interleavings..."),

  NewRevTrace = plan_interleavings_dpor(
                  lists:reverse(RevEarly, Late), [], State),
  
  State#scheduler_state{trace = NewRevTrace};


plan_interleavings(#scheduler_state{algo = Algo} = _State) ->
  exit({"unknown exploration algorithm", Algo}).


% (Events in order, New Trace, Scheduler State)
plan_interleavings_dpor([], ExploredTraces, _SchedulerState) ->
  ExploredTraces;


% Complexity:
% plan_interleavings_dpor      | (N) *
% plan_interleavings_for_event | (N + 1)/2 *
%  |-> get_dependent_action    | (N)
%                              = (N^3 + N^2)/2 = N^3
plan_interleavings_dpor([TraceState|UnexploredRest],
                        ExploredTraces, State) ->
  
  #scheduler_state{
    logger = _Logger,
    non_racing_system = NonRacingSystem
  } = State,
  
  #trace_state{
    done = [Event|_] = _Done,
    index = _Index,
    graph_ref = Ref
  } = TraceState,
  
  #event{
    event_info = _EventInfo, 
    special = Special
  } = Event,
  
  % Should we skip trying to find interleavings of this event.
  % On the command line we can specify --non_racing_system which
  % causes the framework to ignore races for that specific module.
  Skip = case proplists:lookup(system_communication, Special) of
      {system_communication, System} -> lists:member(System, NonRacingSystem);
      none -> false
    end,
  
  case Skip of
    true ->
      plan_interleavings_dpor(UnexploredRest,
                              [TraceState|ExploredTraces], State);
    false ->
      BaseClock = update_actor_clock(Event, State, ExploredTraces),
      GState = State#scheduler_state{current_graph_ref = Ref},
	  
	  % Do the actual planning.	 
      BaseNewOldTrace = plan_interleavings_for_event(
              ExploredTraces, Event, UnexploredRest, BaseClock, GState),
      plan_interleavings_dpor(UnexploredRest,
                              [TraceState|BaseNewOldTrace], State)
  end.


update_actor_clock(Event, SchedState, OldTrace) -> 
  #event{
		 actor = Actor, 
		 event_info = EventInfo
  } = Event,

  #scheduler_state{
     logger = _Logger,
     message_info = MessageInfo
  } = SchedState,
  
  ClockMap = get_base_clock(OldTrace, []),
  StateClock = lookup_clock(state, ClockMap),
  ActorLast = lookup_clock_value(Actor, StateClock),
  ActorClock = orddict:store(Actor, ActorLast, lookup_clock(Actor, ClockMap)),
  case ?is_channel(Actor) of
    true ->
      #message_event{message = #message{id = Id}} = EventInfo,
      message_clock(Id, MessageInfo, ActorClock, ?message_sent);
    false -> ActorClock
  end.
	
plan_interleavings_for_event(ExploredTraces, Event, Later, Clock, State) ->
  plan_interleavings_for_event(ExploredTraces, Event, Later, Clock, State, []).

plan_interleavings_for_event([], _Event, _Later, _Clock, _State, NewOldTrace) ->
  lists:reverse(NewOldTrace);

% Go thr;ough all previous tarce states (ExploredTraces) and see if any of those events 
% are causaly related with the given event (Event).
plan_interleavings_for_event([TraceState|Rest] = _ExploredTraces, Event,
                             Later, Clock, SchedState, NewOldTrace) ->
  
  #trace_state{
     done = [#event{actor = EarlyActor} = EarlyEvent|_],
     index = EarlyIndex
    } = TraceState,
  
  #event{
    actor = _Actor
  } = Event,
  
  
  EarlyClock = lookup_clock_value(EarlyActor, Clock),
  Action = case EarlyIndex > EarlyClock of
      false -> none;
      true -> get_dependent_action(TraceState, Event, Later, Clock, SchedState, NewOldTrace)
    end,
  
  {NewTrace, NewClock} = case Action of
      none -> {[TraceState|NewOldTrace], Clock};
      {update_clock, C} -> {[TraceState|NewOldTrace], C};
      {update, T, C} ->
        log_race(EarlyEvent, Event, SchedState, TraceState),
        %print_debug(green, ["Race Detected"]),
        {T, C}
    end,
  
  plan_interleavings_for_event(Rest, Event, Later, NewClock, SchedState, NewTrace).


get_dependent_action(TraceState, Event, Later, Clock, 
					 #scheduler_state{algo = Algo} = SchedState, Earlier)
  	when Algo =:= transdpor ->
  
  %#scheduler_state{logger = Logger} = State,
  
  #trace_state{
     clock_map = EarlyClockMap,
     done = [#event{actor = EarlyActor} = EarlyEvent|_],
     freeze = Freeze
    } = TraceState,
  
  case concuerror_dependencies:dependent_safe(EarlyEvent, Event) of
    false -> none;	
	
    irreversible ->
      NC = max_cv(lookup_clock(EarlyActor, EarlyClockMap), Clock),
      {update_clock, NC};
	
    true ->
      NC = max_cv(lookup_clock(EarlyActor, EarlyClockMap), Clock),
	  case Freeze of
		true ->
          {update_clock, NC};
		false -> 
		  % Set the freeze flag if not already set.
		  NewTraceState = TraceState#trace_state{freeze = true},
          case update_trace(Event, NewTraceState, Later, Earlier, SchedState) of
            skip ->               {update_clock, NC};
            UpdatedNewOldTrace -> {update, UpdatedNewOldTrace, NC}
          end

	  end

end;

% Complexity:
% update_trace | N
%              = N
get_dependent_action(TraceState, Event, Later, Clock, State, Earlier) ->
  
  %#scheduler_state{logger = Logger} = State,
  
  #trace_state{
     clock_map = EarlyClockMap,
     done = [#event{actor = EarlyActor} = EarlyEvent|_]
    } = TraceState,
  
  case concuerror_dependencies:dependent_safe(EarlyEvent, Event) of
    false -> none;	
	
    irreversible ->
      NC = max_cv(lookup_clock(EarlyActor, EarlyClockMap), Clock),
      {update_clock, NC};
	
    true ->
      NC = max_cv(lookup_clock(EarlyActor, EarlyClockMap), Clock),
      case update_trace(Event, TraceState, Later, Earlier, State) of
        skip ->               {update_clock, NC};
        UpdatedNewOldTrace -> {update, UpdatedNewOldTrace, NC}
      end
end.


% We found two dependent events, time to update the trace.
%
% Complexity:
% not_dep       | (E + L) +
% insert_wakeup | 2(E + L) +
%               = 3(E + L) = 3N = N
update_trace(Event, TraceState, Later, Earlier, State) ->
  #scheduler_state{logger = Logger, optimal = Optimal} = State,
  #trace_state{
     done = [#event{actor = EarlyActor}|Done],
     delay_bound = DelayBound,
     index = EarlyIndex,
     sleeping = Sleeping,
     wakeup_tree = WakeupTree
    } = TraceState,
  
  % Filter non-dependent events.
  NotDep = not_dep(Earlier ++ Later, EarlyActor, EarlyIndex, Event),
  case insert_wakeup(Sleeping ++ Done, WakeupTree, NotDep, Optimal) of
    skip -> skip;
    NewWakeupTree -> case
        (DelayBound =:= infinity) orelse
        (DelayBound - length(Done ++ WakeupTree) > 0)
      of
        true ->
          trace_plan(Logger, EarlyIndex, NotDep),
          % There is a new wake-up tree.
          NS = TraceState#trace_state{wakeup_tree = NewWakeupTree},
          [NS|Earlier];
        false -> skip
      end
  end.


% 1) go over all [Sleeping] events and make sure they ARE NOT dependent with
% NotDep set. If any of them are, return 'skip', otherwise
% 2) go over all [Wakeup] events and make sure they ARE dependent with
% NotDep set. If any of them are not, return 'skip', otherwise return
% a new wakeup tree containing all NotDep.
%
% Complexity: 2N = N
insert_wakeup([Sleeping|Rest], Wakeup, NotDep, Optimal) when Optimal ->
  case dep_free(Sleeping, NotDep) =:= false of
    true  -> insert_wakeup(Rest, Wakeup, NotDep, Optimal);
    false -> skip
  end;

insert_wakeup([], Wakeup, NotDep, Optimal) when Optimal ->
  insert_wakeup(Wakeup, NotDep);


insert_wakeup(Sleeping, Wakeup, [E|_] = NotDep, _Optimal) ->
  Initials = get_initials(NotDep),
  All = Sleeping ++ [W || {W, []} <- Wakeup],
  case existing(All, Initials) of
    true -> skip;
    false -> Wakeup ++ [{E,[]}]
  end.


insert_wakeup([], NotDep) ->
  Fold = fun(Event, Acc) -> [{Event, Acc}] end,
  lists:foldr(Fold, [], NotDep);

insert_wakeup([{Wakeup, []} = Node|Rest], NotDep) ->
  case dep_free(Wakeup, NotDep) of
	
    false -> case insert_wakeup(Rest, NotDep) of
        skip -> skip;
        NewTree -> [Node|NewTree]
      end;
	
    _ -> skip
  
  end;

insert_wakeup([{Wakeup, Deeper} = Node|Rest], NotDep) ->
  case dep_free(Wakeup, NotDep) of
	
    false -> case insert_wakeup(Rest, NotDep) of
        skip -> skip;
        NewTree -> [Node|NewTree]
      end;
	
    NewNotDep -> case insert_wakeup(Deeper, NewNotDep) of
        skip -> skip;
        NewTree -> [{Wakeup, NewTree}|Rest]
      end
  
  end.



% For every event in the trace, where we define an event as:
% (1) An actor calling a BIF (<0.66.0>).
% or (2) A channel message event ({<0.65.0>,<0.38.0>}).
% 
% ... assign it a value from a monotonically increasing vector clock,
% and associate a set of events, such that those events 'happen 
% before' (ordering events based on the potential causal relationship 
% of pairs of events in a trace). This information is stored in ClockMap.
%
% XXX: What the hell is MessageInfo?

assign_happens_before(UntimedLate, RevEarly, State) ->
  assign_happens_before(UntimedLate, [], RevEarly, State).

assign_happens_before([], AlreadyExplored, _RevEarly, _State) ->
  lists:reverse(AlreadyExplored);

% Complexity:
% assign_happens_before | ( L ) *
% happens_before_clock  | ( E + (E + 1)/2 )
%                       = N/2 ( N/2 + (N/2 + 1)/2 )
%                       = N^2
assign_happens_before([TraceState|Later] = _UntimedLate,
                      AlreadyExplored, RevEarly, State) ->
  
  #scheduler_state{
    logger = _Logger,
    message_info = MessageInfo
  } = State,
  
  #trace_state{
    done = [Event|_RestEvents],
    index = Index
  } = TraceState,
  
  #event{
    actor = Actor,
    special = Special
  } = Event,
  
  ClockMap = get_base_clock(AlreadyExplored, RevEarly),
  OldClock = lookup_clock(Actor, ClockMap),
  ActorClock = orddict:store(Actor, Index, OldClock),
  
  BaseHappenedBeforeClock = add_pre_message_clocks(
	    Special, MessageInfo, ActorClock),
  
  HappenedBeforeClock = happens_before_clock(
		AlreadyExplored ++ RevEarly, Event, BaseHappenedBeforeClock, State),
  
  maybe_mark_sent_message(Special, HappenedBeforeClock, MessageInfo),
  maybe_mark_delivered_message(Special, HappenedBeforeClock, MessageInfo),
  
  NewClockMap = update_clock_map(
				  Event, HappenedBeforeClock, ClockMap),
  NewTraceState = update_trace_state(
          Event, HappenedBeforeClock, NewClockMap, TraceState),
  
  assign_happens_before(Later, [NewTraceState|AlreadyExplored], RevEarly, State).



update_trace_state(Event, HappenedBeforeClock, NewClockMap, TraceState) ->
  
  #trace_state{
    done = [Event|RestEvents],
    index = Index
  } = TraceState,
  
  #event{
    actor = Actor
  } = Event,
	
  % 'State Clock' keeps track of each actor and its logical clock. 
  StateClock = lookup_clock(state, NewClockMap),
  
  % Make this Event a part of the HappenedBeforeClock.
  OldActorClock = lookup_clock_value(Actor, StateClock),
  FinalHappenedBeforeClock = orddict:store(Actor, OldActorClock, HappenedBeforeClock),
  
  FinalStateClock = orddict:store(Actor, Index, StateClock),
  FinalClockMap = dict:store(
      Actor, FinalHappenedBeforeClock,
      dict:store(state, FinalStateClock, NewClockMap)),
	
  TraceState#trace_state{
      clock_map = FinalClockMap,
      done = [Event|RestEvents]}.


% Associate HappenedBeforeClock with the current Actor and store it
% in the ClockMap. Also, if this events spawns a new process, make
% sure to also associate the same HappenedBeforeClock with the new PID.

update_clock_map(Event, HappenedBeforeClock, ClockMap) ->
  #event{
	actor = Actor,
	special = Special
  } = Event,

  BaseNewClockMap = dict:store(Actor, HappenedBeforeClock, ClockMap),
  case proplists:lookup(new, Special) of
      {new, SpawnedPid} ->
        dict:store(SpawnedPid, HappenedBeforeClock, BaseNewClockMap);
      none -> BaseNewClockMap
    end.


% Filter non-dependent events.
not_dep(Trace, Actor, Index, Event) ->
  not_dep(Trace, Actor, Index, Event, []).

not_dep([], _Actor, _Index, Event, NotDep) ->
  %% The racing event's effect may differ, so new label.
  lists:reverse([Event#event{label = undefined}|NotDep]);

not_dep([TraceState|Rest], Actor, Index, Event, NotDep) ->
  #trace_state{
     clock_map = ClockMap,
     done = [#event{actor = LaterActor} = LaterEvent|_]
    } = TraceState,
  
  LaterClock = lookup_clock(LaterActor, ClockMap),
  ActorLaterClock = lookup_clock_value(Actor, LaterClock),
  NewNotDep =
    case Index > ActorLaterClock of
      false -> NotDep;
      true -> [LaterEvent|NotDep]
    end,
  not_dep(Rest, Actor, Index, Event, NewNotDep).


% Is actor A already in the wakup tree?
existing([], _) -> false;
existing([#event{actor = A}|Rest], Initials) ->
  Pred = fun(#event{actor = B}) -> A =:= B end,
  case lists:any(Pred, Initials) of
    true -> true;
    false -> existing(Rest, Initials)
  end.  


%% =============================================================================
%% WAKEUP TREE FUNCTIONS
%% =============================================================================

% Explore the current wakeup tree
replay_wakeup_tree(#scheduler_state{
                      trace = [#trace_state{wakeup_tree = WakeupTree}=Last|_]}=State) 
                  when WakeupTree =/= [] ->
  % We have a wakeup tree, which we are replaying.
  % Wakeup trees are of the form
  % [{#event{}, 
  %  [{#event{}, 
  %   [{...}, ...]}, ...]}, Other wakeup trees]
  #trace_state{
     actors      = Actors,
     delay_bound = DelayBound,
     index       = I,
     sleeping    = Sleeping,
     wakeup_tree = WakeupTree
    } = Last,
  % Sort actors, GNE/3 calls actors in order.
  SortedActors = schedule_sort(Actors, State),
  [{#event{actor = Actor, label = Label} = Event, _}|_] = WakeupTree,
  % The actor in this case cannot be sleeping.
  false = lists:member(Actor, Sleeping),
  % See how many scheduling decisions we are screwing up to run this particular actor:
  % can bound the number of such things.
  Delay =
    case DelayBound =/= infinity of
      true -> count_delay(SortedActors, Actor);
      false -> 0
    end,
  {ok, UpdatedEvent} =
    case Label =/= undefined of
      true ->
        NewEvent = get_next_event_backend(Event, State),
        try {ok, Event} = NewEvent
        catch
          _:_ ->
            #scheduler_state{print_depth = PrintDepth} = State,
            Reason = {replay_mismatch, I, Event, element(2, NewEvent), PrintDepth},
            ?crash(Reason)
        end;
      false ->
		%% XXX: In what case is the label set?
        %% Last event = Previously racing event = Result may differ.
        ResetEvent = reset_event(Event),
        get_next_event_backend(ResetEvent, State)
    end,
  % This moves us along in the Wakeup Tree
  UpState = update_state(UpdatedEvent, State#scheduler_state{delay = Delay}),
  replay_wakeup_tree(UpState);

replay_wakeup_tree(#scheduler_state{}=State) ->
  State.


% Given a temporal ordering of events, find a new ordering such that
% no past event is dependent with any future event. Consequently, we're
% allowed to replay the reuslt of this function all at once.
get_initials(TermporalOrdering) ->
  get_initials(TermporalOrdering, [], []).

get_initials([], Initials, _) ->
  lists:reverse(Initials);

get_initials([Event|Rest], Initials, All) ->
  Fun = fun(Initial, Acc) -> Acc andalso
    concuerror_dependencies:dependent_safe(Initial, Event) =:= false
  end,
  
  case lists:foldr(Fun, true, All) of
    true -> get_initials(Rest, [Event|Initials], [Event|All]);
	false -> get_initials(Rest, Initials, [Event|All]) 
  end.        


% Check to if the given event is dependency-free with all events in NotDep.
dep_free(Event, NotDep) ->
  dep_free(Event, NotDep, []).

dep_free(
  	#event{actor = EventActor}, 
  	[#event{actor = EActor}|NotDep], 
	Acc) when EventActor =:= EActor->
  lists:reverse(Acc, NotDep);

dep_free(Event, [E|NotDep], Acc) ->
      case concuerror_dependencies:dependent_safe(Event, E) of
        True when True =:= true; True =:= irreversible -> false;
        false -> dep_free(Event, NotDep, [E|Acc])
      end;

dep_free(_Event, [], Acc) ->
  lists:reverse(Acc).

% Find first trace state that has a wakeup tree.
find_prefix([], _State) -> [];

find_prefix([#trace_state{wakeup_tree = []}|Rest], State) ->
  find_prefix(Rest, State);

find_prefix([#trace_state{graph_ref = Sibling, freeze = Freeze} = Other|Rest], 
#scheduler_state{algo = Algo} = SchedState) when Algo =:= transdpor ->
  
  ?assert(Freeze =:= true),
  #scheduler_state{logger = Logger} = SchedState,
  [#trace_state{graph_ref = Parent}|_] = Rest,
  % Exploring states from this state onwards.
  concuerror_logger:graph_set_node(Logger, Parent, Sibling),
  [Other#trace_state{
    graph_ref = make_ref(),
    clock_map = dict:new(),
	freeze = false}|Rest];

find_prefix([#trace_state{graph_ref = Sibling} = Other|Rest], SchedState) ->
  #scheduler_state{logger = Logger} = SchedState,
  [#trace_state{graph_ref = Parent}|_] = Rest,
  % Exploring states from this state onwards.
  concuerror_logger:graph_set_node(Logger, Parent, Sibling),
  [Other#trace_state{
    graph_ref = make_ref(),
	clock_map = dict:new()}
  |Rest].


%% =============================================================================
%% ENGINE (manipulation of the Erlang processes under the scheduler)
%% =============================================================================

reset_processes(State) ->
  #scheduler_state{
     entry_point = EntryPoint,
     first_process = FirstProcess,
     processes = Processes,
     timeout = Timeout
    } = State,
  Fold =
    fun(?process_pat_pid_kind(P, Kind), _) ->
        case Kind =:= regular of
          true -> P ! reset;
          false -> ok
        end,
        ok
    end,
  ok = ets:foldl(Fold, ok, Processes),
  ok =
    concuerror_callback:start_first_process(FirstProcess, EntryPoint, Timeout).

replay_prefix(Trace, State) ->
  % Just reset processes to their original state, with first process at its entry point.
  reset_processes(State),
  replay_prefix_aux(lists:reverse(Trace), State).

replay_prefix_aux([_], State) ->
  %% Last state has to be properly replayed.
  State;

replay_prefix_aux([#trace_state{done = [Event|_], index = I}|Rest], State) ->
  #scheduler_state{logger = _Logger, print_depth = PrintDepth} = State,
  ?trace(_Logger, "~s~n", [?pretty_s(I, Event)]),
  % Execute the event currently at the head of the prefix.
  {ok, NewEvent} = get_next_event_backend(Event, State),
  try
    true = Event =:= NewEvent
  catch
    _:_ ->
      #scheduler_state{print_depth = PrintDepth} = State,
      ?crash({replay_mismatch, I, Event, NewEvent, PrintDepth})
  end,
  replay_prefix_aux(Rest, maybe_log(Event, State, I)).



%% =============================================================================
%% FUNCTIONS THAT OPERATE ON ACTORS
%% =============================================================================

schedule_sort([], _State) -> [];
schedule_sort(
  Actors,   
  #scheduler_state{
     last_scheduled = LastScheduled,
     scheduling = Scheduling,
     strict_scheduling = StrictScheduling
  } = _State) when Scheduling =:= oldest ->
  
  Sorted = Actors,

  case StrictScheduling of
    false -> [LastScheduled|lists:delete(LastScheduled, Sorted)];
    _ -> Sorted
  end;


schedule_sort([], _State) -> [];
schedule_sort(
  Actors,   
  #scheduler_state{
     last_scheduled = LastScheduled,
     scheduling = Scheduling,
     strict_scheduling = StrictScheduling
  } = _State) when Scheduling =:= newest->
  
  Sorted = lists:rverse(Actors),

  case StrictScheduling of
    false -> [LastScheduled|lists:delete(LastScheduled, Sorted)];
    _ -> Sorted
  end;

schedule_sort([], _State) -> [];
schedule_sort(
  Actors,   
  #scheduler_state{
     last_scheduled = LastScheduled,
     scheduling = Scheduling,
     strict_scheduling = StrictScheduling
  } = _State) when Scheduling =:= round_robin->
  

  Split = fun(E) -> E =/= LastScheduled end,    
  {Pre, Post} = lists:splitwith(Split, Actors),
  Sorted = Post ++ Pre,

  case StrictScheduling of
    true ->
      [LastScheduled|Rest] = Sorted,
      Rest ++ [LastScheduled];
    _ -> 
	  Sorted
  end.


%% =============================================================================
%% UPDATE FUNCTIONS	
%% =============================================================================

% Move things along in the Wakeup Tree and record other things

update_state(#event{special = Special} = Event, State) ->
  #scheduler_state{
     delay  = Delay,
     logger = Logger,
     trace  = [Last|Prev]
    } = State,
  
  #trace_state{
     actors      = Actors,
     delay_bound = DelayBound,
     done        = Done,
     index       = Index,
     graph_ref   = Ref,
     sleeping    = Sleeping,
     wakeup_tree = WakeupTree
    } = Last,
  
  ?trace(Logger, "~s~n", [?pretty_s(Index, Event)]),
  concuerror_logger:graph_new_node(Logger, Ref, Index, Event),
  
  AllSleeping = ordsets:union(ordsets:from_list(Done), Sleeping),
  NextSleeping = update_sleeping(Event, AllSleeping, State),
  
  % NextWakeupTree is what we care about here, tells us where to go next.
  {NewLastWakeupTree, NextWakeupTree} =
    case WakeupTree of
      [] -> {[], []};
      [{_, NWT}|Rest] -> {Rest, NWT}
    end,
  NewLastDone = [Event|Done],
  NewDelayBound =
    case Delay =:= 0 of
      true -> DelayBound;
      false -> DelayBound - Delay
    end,
  InitNextTrace = #trace_state{
       actors      = Actors,
       delay_bound = NewDelayBound,
       index       = Index + 1,
       sleeping    = NextSleeping,
       wakeup_tree = NextWakeupTree
      },
  % Keep track of other possible wake up trees. When this trace is replayed, 
  % from this particular point, the next time we will find "NewLastWakeupTree" 
  % and use that.
  NewLastTrace = Last#trace_state{
	done = NewLastDone,
	wakeup_tree = NewLastWakeupTree
  },
  
  InitNewState = State#scheduler_state{
	trace = [InitNextTrace, NewLastTrace|Prev]
  },
  
  NewState = maybe_log(Event, InitNewState, Index),
  
  update_special(Special, NewState).


update_special(List, State) when is_list(List) ->
  lists:foldl(fun update_special/2, State, List);

update_special(Special, State) ->
  #scheduler_state{message_info = MessageInfo, trace = [Next|Trace]} = State,
  #trace_state{actors = Actors} = Next,
  NewActors =
    case Special of
      halt -> [];
      {message, Message} ->
        add_message(Message, Actors, MessageInfo);
      {message_delivered, MessageEvent} ->
        remove_message(MessageEvent, Actors);
      {message_received, _Message} ->
        Actors;
      {new, SpawnedPid} ->
        Actors ++ [SpawnedPid];
      {system_communication, _} ->
        Actors
    end,
  NewNext = Next#trace_state{actors = NewActors},
  State#scheduler_state{trace = [NewNext|Trace]}.




filter_sleeping([], AvailableActors) -> AvailableActors;
filter_sleeping([#event{actor = Actor}|Sleeping], AvailableActors) ->
  NewAvailableActors =
    case ?is_channel(Actor) of
      true -> lists:keydelete(Actor, 1, AvailableActors);
      false -> lists:delete(Actor, AvailableActors)
    end,
  filter_sleeping(Sleeping, NewAvailableActors).


% Sleep sets prohibit visited transitions from executing again
% until the search explores a dependent transition. Assume that
% the search explores transition t from state s, backtracks t,
% then explores t from s instead. Unless the search explores
% a transition that is dependent with t, no states are reachable
% via t that were not already reachable via t from s. Thus, t
% sleeps unless a dependent transition is explored.
%
% Example: 
% After the search explores t1 and all states reachable via 
% t1 from s, it places t1 in the sleep set for s. No new states
% become reachable via t1 until the search performs a transition 
% that is dependent with t1 . Thus, t1 propagates to the sleep
% set in state s', because t1 <==> t2. When the search explores 
% t3, however, it cannot propagate t1 to the sleep set in s'
% because t1 <=/=> t3 . New states may be reachable via t1 
% from s'', so the search must explore t1 from s''.
update_sleeping(NewEvent, Sleeping, State) ->
  #scheduler_state{logger = _Logger} = State,
  Pred =
    fun(OldEvent) ->
        V = concuerror_dependencies:dependent_safe(OldEvent, NewEvent),
        ?trace(_Logger, "     Awaking (~p): ~s~n", [V,?pretty_s(OldEvent)]),
        V =:= false
    end,
  lists:filter(Pred, Sleeping).


%% =============================================================================
%% CLOCK FUNCTIONS
%% =============================================================================

lookup_clock(P, ClockMap) ->
  case dict:find(P, ClockMap) of
    {ok, Clock} -> Clock;
    error -> orddict:new()
  end.

lookup_clock_value(P, CV) ->
  case orddict:find(P, CV) of
    {ok, Value} -> Value;
    error -> 0
  end.

get_base_clock(RevLate, RevEarly) ->
  try
    get_base_clock(RevLate)
  catch
    throw:none ->
      try
        get_base_clock(RevEarly)
      catch
        throw:none -> dict:new()
      end
  end.

get_base_clock([]) -> throw(none);
get_base_clock([#trace_state{clock_map = ClockMap}|_]) -> ClockMap.

% Go through 'Specials' and for each event that's of type:
% 
% Message_delivered:
% See if this message has been previously sent. If it has, this means that it
% 'happened before' message_sent event, so consequently thake the max (merge)
% those two sets clocks.
% 
% Message received:
% Same thing as above, except look for the message_sent event.
%
% All messages events have the following causal relationship:
%  Message Sent -> Message Delivered -> Message Received.  
%
add_pre_message_clocks([], _, Clock) -> Clock;
add_pre_message_clocks([Special|Specials], MessageInfo, Clock) ->
  NewClock =
    case Special of
      {message_received, Id} ->
	    message_clock(Id, MessageInfo, Clock, ?message_delivered);
      {message_delivered, #message_event{message = #message{id = Id}}} ->
        message_clock(Id, MessageInfo, Clock, ?message_sent);
      _ -> Clock
    end,
  add_pre_message_clocks(Specials, MessageInfo, NewClock).

message_clock(Id, MessageInfo, ActorClock, MessageType) ->
  case ets:lookup_element(MessageInfo, Id, MessageType) of
    undefined -> ActorClock;
    HappenedBeforeClock -> max_cv(ActorClock, HappenedBeforeClock)
  end.

% This function iterates through all old trace states, and checks to see
% if any of those earlier events are dependent on the CurrentEvent.
%
% If FALSE, just pass the exisintg CurrentActorClock the the next recursive call.
%
% If TRUE, take the EarlyActorClock and merge it with the CurrentActorClock
% Pass the result to the next recursive call as a new CurrentActorClock.
%
% This function effectively creates 'happens before' clock for the CurrentEvent.
%
% Complexity: N
happens_before_clock([], _Event, ActorClock, _State) ->
  ActorClock;

happens_before_clock([TraceState|Rest], CurrentEvent, CurrentActorClock, State) ->
  
  #scheduler_state{
    assume_racing = AssumeRacing
  } = State,
  
  #trace_state{
     done = [#event{actor = EarlyActor} = EarlyEvent|_],
     clock_map = ClockMap,
     index = EarlyIndex
    } = TraceState,
   
  EarlyClock = lookup_clock_value(EarlyActor, CurrentActorClock),

  NewClock = case EarlyIndex > EarlyClock of
      false -> CurrentActorClock;
      true ->
        Dependent = concuerror_dependencies:dependent(
                    EarlyEvent, CurrentEvent, AssumeRacing),
        print_trace(State, TraceState, Dependent),
		
        case Dependent of
          false -> CurrentActorClock;
          True when True =:= true; True =:= irreversible ->
            EarlyActorClock = lookup_clock(EarlyActor, ClockMap),
            max_cv(CurrentActorClock,
                   orddict:store(EarlyActor, EarlyIndex, EarlyActorClock))
        end
    end,
  
  happens_before_clock(Rest, CurrentEvent, NewClock, State).


maybe_mark_delivered_message(Special, HappenedBeforeClock, MessageInfo) ->
  case proplists:lookup(message_delivered, Special) of
    none -> true;
    {message_delivered, MessageEvent} ->
      #message_event{message = #message{id = Id}} = MessageEvent,
      Delivery = {?message_delivered, HappenedBeforeClock},
      ets:update_element(MessageInfo, Id, Delivery)
  end.

% Remember, there are three special types of message events:
% {message, ...}, {message_delivered, ...}, {message_received, ...}
%
% If any of types is {message, ...}, this means that a new message has
% been sent. Conseqently, update the ETS with 'Id' and 'HappenedBeforeClock'.
maybe_mark_sent_message(Special, HappenedBeforeClock, MessageInfo) 
  						when is_list(Special)->
  Message = proplists:lookup(message, Special),
  maybe_mark_sent_message(Message, HappenedBeforeClock, MessageInfo);

maybe_mark_sent_message({message, Message}, HappenedBeforeClock, MessageInfo) ->
  #message_event{message = #message{id = Id}} = Message,
  ets:update_element(MessageInfo, Id, {?message_sent, HappenedBeforeClock});

maybe_mark_sent_message(_, _, _) -> true.

%% =============================================================================
%% MESSAGE FUNCTIONS
%% =============================================================================

add_message(MessageEvent, Actors, MessageInfo) ->
  #message_event{
     message = #message{id = Id},
     recipient = Recipient,
     sender = Sender
    } = MessageEvent,
  Channel = {Sender, Recipient},
  Update = fun(Queue) -> queue:in(MessageEvent, Queue) end,
  Initial = queue:from_list([MessageEvent]),
  ets:insert(MessageInfo, ?new_message_info(Id)),
  insert_message(Channel, Update, Initial, Actors).

insert_message(Channel, Update, Initial, Actors) ->
  insert_message(Channel, Update, Initial, Actors, false, []).

insert_message(Channel, _Update, Initial, [], Found, Acc) ->
  case Found of
    true -> lists:reverse(Acc, [{Channel, Initial}]);
    false -> [{Channel, Initial}|lists:reverse(Acc)]
  end;
insert_message(Channel, Update, _Initial, [{Channel, Queue}|Rest], true, Acc) ->
  NewQueue = Update(Queue),
  lists:reverse(Acc, [{Channel, NewQueue}|Rest]);
insert_message({From, _} = Channel, Update, Initial, [Other|Rest], Found, Acc) ->
  case Other of
    {{_,_},_} ->
      insert_message(Channel, Update, Initial, Rest, Found, [Other|Acc]);
    From ->
      insert_message(Channel, Update, Initial, Rest,  true, [Other|Acc]);
    _ ->
      case Found of
        false ->
          insert_message(Channel, Update, Initial, Rest, Found, [Other|Acc]);
        true ->
          lists:reverse(Acc, [{Channel, Initial},Other|Rest])
      end
  end.

remove_message(#message_event{recipient = Recipient, sender = Sender}, Actors) ->
  Channel = {Sender, Recipient},
  remove_message(Channel, Actors, []).

remove_message(Channel, [{Channel, Queue}|Rest], Acc) ->
  NewQueue = queue:drop(Queue),
  case queue:is_empty(NewQueue) of
    true  -> lists:reverse(Acc, Rest);
    false -> lists:reverse(Acc, [{Channel, NewQueue}|Rest])
  end;
remove_message(Channel, [Other|Rest], Acc) ->
  remove_message(Channel, Rest, [Other|Acc]).

assert_no_messages() ->
  receive
    Msg -> error({pending_message, Msg})
  after
    0 -> ok
  end.

%% =============================================================================
%% HELPER FUNCTIONS
%% =============================================================================

max_cv(D1, D2) ->
  Merger = fun(_Key, V1, V2) -> max(V1, V2) end,
  orddict:merge(Merger, D1, D2).


-spec explain_error(term()) -> string().

explain_error(first_interleaving_crashed) ->
  {
    io_lib:format(
      "The first interleaving of your test had errors. Check the output file."
      " You may then use -i to tell Concuerror to continue or use other options"
      " to filter out the reported errors, if you consider them acceptable"
      " behaviours.",
      []),
    warning};
explain_error({replay_mismatch, I, Event, NewEvent, Depth}) ->
  [EString, NEString] =
    [concuerror_printer:pretty_s(E, Depth) || E <- [Event, NewEvent]],
  [Original, New] =
    case EString =/= NEString of
      true -> [EString, NEString];
      false ->
        [io_lib:format("~p",[E]) || E <- [Event, NewEvent]]
    end,
  io_lib:format(
    "On step ~p, replaying a built-in returned a different result than"
    " expected:~n"
    "  original: ~s~n"
    "  new     : ~s~n"
    ?notify_us_msg,
    [I,Original,New]
   ).

filter_warnings(Warnings, []) -> Warnings;
filter_warnings(Warnings, [Ignore|Rest] = Ignored) ->
  case lists:keytake(Ignore, 1, Warnings) of
    false -> filter_warnings(Warnings, Rest);
    {value, _, NewWarnings} -> filter_warnings(NewWarnings, Ignored)
  end.

count_delay(Actors, Actor) ->
  count_delay(Actors, Actor, 0).

count_delay([{Actor,_}|_], Actor, N) -> N;

count_delay([Actor|_], Actor, N) -> N;

count_delay([Channel|Rest], Actor, N) when ?is_channel(Channel) ->
  count_delay(Rest, Actor, N+1);

count_delay([Other|Rest], Actor, N) ->
  NN =
    case concuerror_callback:enabled(Other) of
      true -> N+1;
      false -> N
    end,
  count_delay(Rest, Actor, NN).


split_trace(RevTrace) ->
  split_trace(RevTrace, []).

split_trace([], UntimedLate) ->
  {[], UntimedLate};

split_trace([#trace_state{clock_map = ClockMap} = State|RevEarlier] = RevEarly,
            UntimedLate) ->
  case dict:size(ClockMap) =:= 0 of
    true  -> split_trace(RevEarlier, [State|UntimedLate]);
    false -> {RevEarly, UntimedLate}
  end.

%% =============================================================================
%% LOGGING FUNCTIONS
%% =============================================================================

log_trace(State) ->
  #scheduler_state{
     current_warnings = UnfilteredWarnings,
     ignore_error = Ignored,
     logger = Logger} = State,
  Warnings = filter_warnings(UnfilteredWarnings, Ignored),
  case UnfilteredWarnings =/= Warnings of
    true ->
      Message = "Some errors were ignored ('--ignore_error').~n",
      ?unique(Logger, ?lwarning, Message, []);
    false ->
      ok
  end,
  Log =
    case Warnings =:= [] of
      true -> none;
      false ->
        TraceInfo =
          case Warnings =:= [sleep_set_block] of
            true -> [];
            false ->
              #scheduler_state{trace = Trace} = State,
              Fold =
                fun(#trace_state{done = [A|_], index = I}, Acc) ->
                    [{I, A}|Acc]
                end,
              lists:foldl(Fold, [], Trace)
          end,
        {lists:reverse(Warnings), TraceInfo}
    end,
  concuerror_logger:complete(Logger, Log),
  case (not State#scheduler_state.ignore_first_crash) andalso (Log =/= none) of
    true -> ?crash(first_interleaving_crashed);
    false ->
      State#scheduler_state{ignore_first_crash = true, current_warnings = []}
  end.

maybe_log(#event{actor = P} = Event, State0, Index) ->
  #scheduler_state{logger = Logger, treat_as_normal = Normal} = State0,
  State = 
    case is_pid(P) of
      true -> State0#scheduler_state{last_scheduled = P};
      false -> State0
    end,
  case Event#event.event_info of
    #exit_event{reason = Reason} = Exit when Reason =/= normal ->
      {Tag, WasTimeout} =
        if is_tuple(Reason), size(Reason) > 0 ->
            T = element(1, Reason),
            {T, T =:= timeout};
           true -> {Reason, false}
        end,
      case is_atom(Tag) andalso lists:member(Tag, Normal) of
        true ->
          ?unique(Logger, ?lwarning, msg(treat_as_normal), []),
          State;
        false ->
          if WasTimeout -> ?unique(Logger, ?ltip, msg(timeout), []);
             Tag =:= shutdown -> ?unique(Logger, ?ltip, msg(shutdown), []);
             true -> ok
          end,
          #event{actor = Actor} = Event,
          Warnings = State#scheduler_state.current_warnings,
          Stacktrace = Exit#exit_event.stacktrace,
          NewWarnings = [{crash, {Index, Actor, Reason, Stacktrace}}|Warnings],
          State#scheduler_state{current_warnings = NewWarnings}
      end;
    #builtin_event{mfargs = {erlang, exit, [_,Reason]}}
      when Reason =/= normal ->
      ?unique(Logger, ?ltip, msg(signal), []),
      State;
    _ -> State
  end.

trace_plan(_Logger, _Index, _NotDep) ->
  ?debug(
     _Logger, "     PLAN~n~s",
     begin
       Indices = lists:seq(_Index, _Index + length(_NotDep) - 1),
       IndexedNotDep = lists:zip(Indices, _NotDep),
       [lists:append(
          [io_lib:format("        ~s~n", [?pretty_s(I,S)])
           || {I,S} <- IndexedNotDep])]
     end).



%%==============================================================================

msg(signal) ->
  "An abnormal exit signal was sent to a process. This is probably the worst"
    " thing that can happen race-wise, as any other side-effecting"
    " operation races with the arrival of the signal. If the test produces"
    " too many interleavings consider refactoring your code.~n";
msg(shutdown) ->
  "A process crashed with reason 'shutdown'. This may happen when a"
    " supervisor is terminating its children. You can use '--treat_as_normal"
    " shutdown' if this is expected behaviour.~n";
msg(sleep_set_block) ->
  "Some interleavings were 'sleep-set blocked'. This is expected if you have"
    " specified '--optimal false', but reveals wasted effort.~n";
msg(timeout) ->
  "A process crashed with reason '{timeout, ...}'. This may happen when a"
    " call to a gen_server (or similar) does not receive a reply within some"
    " standard timeout. Use the '--after_timeout' option to treat after clauses"
    " that exceed some threshold as 'impossible'.~n";
msg(treat_as_normal) ->
  "Some abnormal exit reasons were treated as normal (--treat_as_normal).~n".


  
  
print_debug(red, Msg) ->
  io:format("\e[1;31m~p\e[m~n~n", Msg);

print_debug(green, Msg) ->
  io:format("\e[1;32m~p\e[m~n~n", Msg);

print_debug(yellow, Msg) ->
  io:format("\e[1;33m~p\e[m~n~n", Msg);

print_debug(blue, Msg) ->
  io:format("\e[1;34m~p\e[m~n~n", Msg);

print_debug(purple, Msg) ->
  io:format("\e[1;35m~p\e[m~n~n", Msg).

print_trace(SchedState, TraceState, Dependent) ->

  #trace_state{
     done = [EarlyEvent|_],
     index = EarlyIndex
    } = TraceState,
   
  
   ?trace(SchedState#scheduler_state.logger,
   	 "    ~s ~s~n",
     begin
  	    Star = fun(false) -> " ";(_) -> "*" end,
        [Star(Dependent), ?pretty_s(EarlyIndex, EarlyEvent)]
 	 end).




log_race(EarlyEvent, Event, SchedState, TraceState) ->
    #scheduler_state{
	  logger = Logger
	} = SchedState,
	
  if SchedState#scheduler_state.show_races ->
    ?unique(Logger, ?lrace,
       "You can disable race pair messages with '--show_races false'~n",
       []),
      EarlyRef = TraceState#trace_state.graph_ref,
      Ref = SchedState#scheduler_state.current_graph_ref,
      concuerror_logger:graph_race(Logger, EarlyRef, Ref),
      concuerror_logger:race(Logger, EarlyEvent, Event);
    true -> ok
  end.
