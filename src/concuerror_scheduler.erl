%% -*- erlang-indent-level: 2 -*-

-module(concuerror_scheduler).

%% User interface
-export([run/1, explain_error/1]).

%%------------------------------------------------------------------------------

%%-define(DEBUG, true).
-define(CHECK_ASSERTIONS, true).
-include("concuerror.hrl").

%%------------------------------------------------------------------------------

%% -type clock_vector() :: orddict:orddict(). %% orddict(pid(), index()).
-type clock_map()    :: dict(). %% dict(pid(), clock_vector()).

%%------------------------------------------------------------------------------

%% =============================================================================
%% DATA STRUCTURES
%% =============================================================================

-type event_tree() :: [{event(), event_tree()}].

-record(trace_state, {
          actors      = []         :: [pid() | {channel(), queue()}],
          clock_map   = dict:new() :: clock_map(),
          delay_bound = infinity   :: bound(),
          done        = []         :: [event()],
          index       = 1          :: index(),
          graph_ref   = make_ref() :: reference(),
          sleeping    = []         :: [event()],
          wakeup_tree = []         :: event_tree()
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

% Out of bounds!
explore(#scheduler_state{current_warnings = Warnings,
				   depth_bound = Bound,
				   trace = [#trace_state{index = I}|Old]} = State)
    when I =:= Bound + 1->
	  
	  StateBounds = State#scheduler_state{
      	current_warnings = [{depth_bound, Bound}|Warnings],
      	trace = Old
      },
	  UpdatedState = update_state(StateBounds),
      {HasMore, NewState} = new_dpor_exploration(UpdatedState),
      case HasMore of
        true -> explore(NewState);
        false -> ok
      end;


explore(#scheduler_state{current_warnings = Warnings,
				   trace = Traces} = State) ->
  
  [CurrentTrace|Old] = Traces,
  #trace_state{
			   actors = CurActors,
			   index = _Index
			  } = CurrentTrace,
  
  {Status, UpdatedEvent} = try
      % Change get_next_event to remove replay dependency on wakeup trees.
      % Perhaps split into three pieces
      % - Round robin scheduler
      % - WUT scheduler
      % - Replay scheduler.
      % DPOR is then replay followed by WUT followed by round robin.

	  {Event, Actors, ScheduledState} = schedule_actors(State),
	  get_next_event(Event, Actors, ScheduledState)

    catch
      exit:Reason -> {{crash, Reason}, State}
    end,
  
  case Status of
    ok ->
	  UpdatedState = update_state(UpdatedEvent, State),
	  explore(UpdatedState);
	
    none ->
 	  UpdatedState = update_state(State),
      {HasMore, NewState} = new_dpor_exploration(UpdatedState),
      case HasMore of
        true -> explore(NewState);
        false -> ok
      end;
	
    {crash, Why} ->
      FatalCrashState = State#scheduler_state{
          current_warnings = [fatal|Warnings],
          trace = Old
      },
	  
      catch log_trace(FatalCrashState),
      exit(Why)
  end.


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
  
  % Sort actors, GNE/3 calls actors in order.
  SortedActors = schedule_sort(Actors, State),
  AvailableActors = filter_sleeping(Sleeping, SortedActors),
  % Run through Actors in round robin order. 
  % Allocate an event to hold data about what happened
  Event = #event{label = make_ref()},
  %get_next_event(Event, System ++ AvailableActors, State#scheduler_state{delay = 0}).
  {Event, System ++ AvailableActors, State#scheduler_state{delay = 0}}.


%% get_next_event(Event, Actors, SchedulerState);
%% Call next actor in order.

%% If we have a channel just deliver it.
get_next_event(Event, [{Channel, Queue}|_], State) ->
  %% Pending messages can always be sent
  MessageEvent = queue:get(Queue),
  UpdatedEvent = Event#event{actor = Channel, event_info = MessageEvent},
  % This will always be ok, FinalEvent since messages are never blocked.
  get_next_event_backend(UpdatedEvent, State); 
  %update_state(FinalEvent, State);
  %{ok, FinalEvent};

% If the first thing is a process then
get_next_event(Event, [P|ActiveProcesses], State) ->
  % Try calling process. 
  case get_next_event_backend(Event#event{actor = P}, State) of
    % If blocked, try remaining processes.
    retry -> get_next_event(Event, ActiveProcesses, State);
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


%% =============================================================================
%% HIGH LEVEL SCHEDULING FUNCTIONS
%% =============================================================================

new_dpor_exploration(State) ->
  % Done exploring one branch, figure out what to do next. In particular what this
  % does is finds when races have been discovered, etc.
  RacesDetectedState = plan_more_interleavings(State),
  LogState = log_trace(RacesDetectedState),
  #scheduler_state{trace = NewTrace} = LogState,
  
  %#trace_state{wakeup_tree = WUT} = NewTrace,
  %io:format("Trace size: ~p~n", [length(NewTrace)]),

  % Once we have figured out a new trace, get things ready to replay. What this does
  % is very simple:
  % (a) Find a starting point/state from which the trace should be explored.
  % (b) Go through all states starting from this point.
  % (c) Execute the set of steps in the wakeup tree so that a race is likely.
  % (b) Replay from this point to find a race.
  has_more_to_explore(LogState).


has_more_to_explore(State) ->
  #scheduler_state{logger = Logger, trace = Trace} = State,
  % Find the first state from which we expect to find a race 
  % (i.e., which has a wake up tree).
  TracePrefix = find_prefix(Trace, State),
  
  %io:format("~nTracePrefix          ~p~n~n", [TracePrefix]),
  
  case TracePrefix =:= [] of
    true -> {false, State#scheduler_state{trace = []}};
    false ->

      ?time(Logger, "New interleaving. Replaying..."),
      % Get us to the state where we can use the wakeup tree to 
	  % examine a potential race.
	  print_debug(yellow, ["Replaying " 
						  ++ integer_to_list(length(TracePrefix)) 
						  ++ " events"]),
      NewState = replay_prefix(TracePrefix, State),
	  print_debug(yellow, ["Replay done"]),
	  
      ?debug(Logger, "~s~n",["Replay done."]),
	  
	  
      PreWUTState = NewState#scheduler_state{trace = TracePrefix},
      % Replay the wakeup tree
      FinalState = replay_wakeup_tree(PreWUTState),
      {true, FinalState}
  end.


plan_more_interleavings(State) ->
  print_debug(red, ["================ new exploration ================"]),

  #scheduler_state{logger = Logger, trace = RevTrace} = State,
  ?time(Logger, "Assigning happens-before..."),
  % Split into half which has timing information and half which does not.
  {RevEarly, UntimedLate} = split_trace(RevTrace),
  
  % Assign happens before to everything. In other words find races.
  Late = assign_happens_before(UntimedLate, RevEarly, State),
  
  print_debug(blue, ["================ RevEarly "
				   ++ integer_to_list(length(RevEarly)) 
				   ++ " | Late "
				   ++ integer_to_list(length(Late))]),

  %?time(Logger, "Planning more interleavings..."),

  NewRevTrace = plan_more_interleavings(lists:reverse(RevEarly, Late), [], State),
  State#scheduler_state{trace = NewRevTrace}.


% (Events in order, New Trace, Scheduler State)
plan_more_interleavings([], OldTrace, _SchedulerState) ->
  OldTrace;

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
plan_more_interleavings([TraceState|Rest] = Trace, OldTrace, State) ->
  #scheduler_state{
     logger = _Logger,
     message_info = MessageInfo,
     non_racing_system = NonRacingSystem
    } = State,
  
  #trace_state{
		     done = [Event|_] = Done, 
		     index = _Index, 
             graph_ref = Ref
  } = TraceState,
  
  #event{
		 actor = Actor, 
		 event_info = EventInfo, 
		 special = Special
  } = Event,
  
  % Should we skip trying to find interleavings of this event.
  Skip = case proplists:lookup(system_communication, Special) of
      {system_communication, System} -> lists:member(System, NonRacingSystem);
      none -> false
    end,
  
  case Skip of
    true ->
      % Skipping
      plan_more_interleavings(Rest, [TraceState|OldTrace], State);
    false ->
	  % ===== Update the vector clocks (Start). =====
      ClockMap = get_base_clock(OldTrace, []),
      StateClock = lookup_clock(state, ClockMap),
      ActorLast = lookup_clock_value(Actor, StateClock),
      ActorClock = orddict:store(Actor, ActorLast, lookup_clock(Actor, ClockMap)),
      BaseClock = case ?is_channel(Actor) of
          true ->
            #message_event{message = #message{id = Id}} = EventInfo,
            message_clock(Id, MessageInfo, ActorClock);
          false -> ActorClock
        end,
	  % ===== Update the vector clocks (End). =====

	  %io:format("ClockMap    ~p~n",  [ClockMap]),
	  %io:format("StateClock  ~p~n",  [StateClock]),
	  %io:format("ActorLast   ~p~n",  [ActorLast]),
	  %io:format("ActorClock  ~p~n",  [ActorClock]),
	  %io:format("BaseClock   ~p~n",  [BaseClock]),
	  %case length(Done) > 1 of
	  %  true -> io:format("Done ~p~n", [Done]);
      %  false -> ok
	  %end,
	  
      ?debug(_Logger, "~s~n", [?pretty_s(_Index, Event)]),
      GState = State#scheduler_state{current_graph_ref = Ref},
	  
	  % Do the actual planning.	 
      BaseNewOldTrace = more_interleavings_for_event(
						  OldTrace, Event, Rest, BaseClock, GState),
      plan_more_interleavings(Rest, [TraceState|BaseNewOldTrace], State)
  end.

print_debug(red, Msg) ->
  io:format("\e[1;31m~p\e[m~n~n", Msg);

print_debug(green, Msg) ->
  io:format("\e[1;32m~p\e[m~n~n", Msg);

print_debug(yellow, Msg) ->
  io:format("\e[1;33m~p\e[m~n~n", Msg);

print_debug(blue, Msg) ->
  io:format("\e[1;34m~p\e[m~n~n", Msg).

	

more_interleavings_for_event(OldTrace, Event, Later, Clock, State) ->
  more_interleavings_for_event(OldTrace, Event, Later, Clock, State, []).

more_interleavings_for_event([], _Event, _Later, _Clock, _State, NewOldTrace) ->
  lists:reverse(NewOldTrace);

% Go through all previous tarce states (OldTraceStates) and see if any of those events 
% are causaly related with the given event (Event).
more_interleavings_for_event(
  	[TraceState|Rest] = OldTraceStates, Event, 
	Later, Clock, State, NewOldTrace) ->
  
  #scheduler_state{
	  logger = Logger
	} = State,
  
  #trace_state{
     clock_map = EarlyClockMap,
     done = [#event{actor = EarlyActor} = EarlyEvent|_],
     index = EarlyIndex
    } = TraceState,
  
  #event{actor = _Actor} = Event,
  
  %io:format("OldTrace  ~p~n",  [length(OldTrace)]),
  %io:format("EarlyEvent  ~p~n",  [EarlyEvent]),
  
  EarlyClock = lookup_clock_value(EarlyActor, Clock),
  Action = case EarlyIndex > EarlyClock of
      false -> none;
      true ->
        Dependent =
          concuerror_dependencies:dependent_safe(EarlyEvent, Event),
        case Dependent of
          false -> none;
          irreversible ->
            NC = max_cv(lookup_clock(EarlyActor, EarlyClockMap), Clock),
            {update_clock, NC};
          true ->
            ?debug(Logger, "   races with ~s~n",
                   [?pretty_s(EarlyIndex, EarlyEvent)]),
            NC = max_cv(lookup_clock(EarlyActor, EarlyClockMap), Clock),
            case update_trace(Event, TraceState, Later, NewOldTrace, State) of
              skip -> {update_clock, NC};
              UpdatedNewOldTrace ->
                concuerror_logger:plan(Logger),
                {update, UpdatedNewOldTrace, NC}
            end
        end
    end,
  
  {NewTrace, NewClock} =
    case Action of
      none -> {[TraceState|NewOldTrace], Clock};
      {update_clock, C} -> {[TraceState|NewOldTrace], C};
      {update, S, C} -> if State#scheduler_state.show_races ->
            ?unique(Logger, ?lrace,
               "You can disable race pair messages with '--show_races false'~n",
               []),
            EarlyRef = TraceState#trace_state.graph_ref,
            Ref = State#scheduler_state.current_graph_ref,
            concuerror_logger:graph_race(Logger, EarlyRef, Ref),
            concuerror_logger:race(Logger, EarlyEvent, Event);
           true -> ok
        end,
		print_debug(green, ["Race Detected"]),
        {S, C}
    end,
  more_interleavings_for_event(Rest, Event, Later, NewClock, State, NewTrace).

%% =============================================================================
%% CAUSAL ANALYSIS
%% =============================================================================

% For every event in the trace, where we define an event as: 
% 	 (1) An actor calling a BIF (<0.66.0>).
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

assign_happens_before([], RevLate, _RevEarly, _State) ->
  lists:reverse(RevLate);

assign_happens_before([TraceState|Later], RevLate, RevEarly, State) ->
  #scheduler_state{logger = _Logger, message_info = MessageInfo} = State,
  #trace_state{done = [Event|RestEvents], index = Index} = TraceState,
  #event{actor = Actor, special = Special} = Event,
  
  ClockMap = get_base_clock(RevLate, RevEarly),
  OldClock = lookup_clock(Actor, ClockMap),
  ActorClock = orddict:store(Actor, Index, OldClock),
  
  %io:format("================================~n"),
  %io:format("Actor          -> ~p~n", [Actor]),
  %io:format("Event Location -> ~p~n", [Location]),
  %io:format("ClockMap Keys  -> ~p~n", [dict:fetch_keys(ClockMap)]),
  %io:format("HB             -> ~s~n", [?pretty_s(Index,Event)]),
  %io:format("HB             -> ~p~n", [Event]),
  %io:format("OldClock       -> ~p~n", [OldClock]),
  %io:format("ActorClock      -> ~p~n", [ActorClock]),
  %io:format("MessageInfo    -> ~p~n", [MessageInfo]),

  BaseHappenedBeforeClock =
    add_pre_message_clocks(Special, MessageInfo, ActorClock),
  
  HappenedBeforeClock =
    update_clock(RevLate++RevEarly, Event, BaseHappenedBeforeClock, State),
  
  maybe_mark_sent_message(Special, HappenedBeforeClock, MessageInfo),
    
  %io:format("BaseHappenedBeforeClock  -> ~p~n", [BaseHappenedBeforeClock]),
  %io:format("HappenedBeforeClock  -> ~p~n", [HappenedBeforeClock]),
  %io:format("Special        -> ~p~n", [Special]),

  case proplists:lookup(message_delivered, Special) of
    none -> true;
    {message_delivered, MessageEvent} ->
      #message_event{message = #message{id = Id}} = MessageEvent,
      Delivery = {?message_delivered, HappenedBeforeClock},
      ets:update_element(MessageInfo, Id, Delivery)
  end,
  
  BaseNewClockMap = dict:store(Actor, HappenedBeforeClock, ClockMap),
  NewClockMap = case proplists:lookup(new, Special) of
      {new, SpawnedPid} ->
        dict:store(SpawnedPid, HappenedBeforeClock, BaseNewClockMap);
      none -> BaseNewClockMap
    end,
  
  % 'State Clock' keeps track of each actor and its logical clock. 
  StateClock = lookup_clock(state, ClockMap),
  OldActorClock = lookup_clock_value(Actor, StateClock),
  FinalActorClock = orddict:store(Actor, OldActorClock, HappenedBeforeClock),
  FinalStateClock = orddict:store(Actor, Index, StateClock),
  FinalClockMap = dict:store(
      Actor, FinalActorClock,
      dict:store(state, FinalStateClock, NewClockMap)),
  NewTraceState = TraceState#trace_state{
      clock_map = FinalClockMap,
      done = [Event|RestEvents]},
  
  assign_happens_before(Later, [NewTraceState|RevLate], RevEarly, State).


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

insert_wakeup(Sleeping, Wakeup, [E|_] = NotDep, Optimal) ->
  case Optimal of
    true -> insert_wakeup(Sleeping, Wakeup, NotDep);
    false ->
      Initials = get_initials(NotDep),
      All = Sleeping ++ [W || {W, []} <- Wakeup],
      case existing(All, Initials) of
        true -> skip;
        false -> Wakeup ++ [{E,[]}]
      end
  end.      

insert_wakeup([Sleeping|Rest], Wakeup, NotDep) ->
  case check_initial(Sleeping, NotDep) =:= false of
    true  -> insert_wakeup(Rest, Wakeup, NotDep);
    false -> skip
  end;

insert_wakeup([], Wakeup, NotDep) ->
  insert_wakeup(Wakeup, NotDep).

insert_wakeup([], NotDep) ->
  Fold = fun(Event, Acc) -> [{Event, Acc}] end,
  lists:foldr(Fold, [], NotDep);

insert_wakeup([{Event, Deeper} = Node|Rest], NotDep) ->
  case check_initial(Event, NotDep) of
    false ->
      case insert_wakeup(Rest, NotDep) of
        skip -> skip;
        NewTree -> [Node|NewTree]
      end;
    NewNotDep ->
      case Deeper =:= [] of
        true  -> skip;
        false ->
          case insert_wakeup(Deeper, NewNotDep) of
            skip -> skip;
            NewTree -> [{Event, NewTree}|Rest]
          end
      end
  end.

get_initials(NotDeps) ->
  get_initials(NotDeps, [], []).

get_initials([], Initials, _) ->
  lists:reverse(Initials);

get_initials([Event|Rest], Initials, All) ->
  Fold =
    fun(Initial, Acc) ->
        Acc andalso
          concuerror_dependencies:dependent_safe(Initial, Event) =:= false
    end,
  NewInitials =
    case lists:foldr(Fold, true, All) of
      true -> [Event|Initials];
      false -> Initials
    end,
  get_initials(Rest, NewInitials, [Event|All]).            


% Check to if the given event is dependent with any events in NotDep.
check_initial(Event, NotDep) ->
  check_initial(Event, NotDep, []).

check_initial(_Event, [], Acc) ->
  lists:reverse(Acc);

check_initial(Event, [E|NotDep], Acc) ->
  #event{actor = EventActor} = Event,
  #event{actor = EActor} = E,
  
  case EventActor =:= EActor of
    true -> lists:reverse(Acc,NotDep);
    false ->
      case concuerror_dependencies:dependent_safe(Event, E) of
        True when True =:= true; True =:= irreversible -> false;
        false -> check_initial(Event, NotDep, [E|Acc])
      end
  end.

% Find first trace state that has a wakeup tree.
find_prefix([], _State) -> [];

find_prefix([#trace_state{wakeup_tree = []}|Rest], State) ->
  find_prefix(Rest, State);

find_prefix([#trace_state{graph_ref = Sibling} = Other|Rest], State) ->
  #scheduler_state{logger = Logger} = State,
  [#trace_state{graph_ref = Parent}|_] = Rest,
  % Exploring states from this state onwards.
  concuerror_logger:graph_set_node(Logger, Parent, Sibling),
  [Other#trace_state{graph_ref = make_ref(), clock_map = dict:new()}|Rest].


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
schedule_sort(Actors, State) ->
  #scheduler_state{
     last_scheduled = LastScheduled,
     scheduling = Scheduling,
     strict_scheduling = StrictScheduling
    } = State,
  Sorted =
    case Scheduling of
      oldest -> Actors;
      newest -> lists:reverse(Actors);
      round_robin ->
        Split = fun(E) -> E =/= LastScheduled end,    
        {Pre, Post} = lists:splitwith(Split, Actors),
        Post ++ Pre
    end,
  case StrictScheduling of
    true when Scheduling =:= round_robin ->
      [LastScheduled|Rest] = Sorted,
      Rest ++ [LastScheduled];
    false when Scheduling =/= round_robin ->
      [LastScheduled|lists:delete(LastScheduled, Sorted)];
    _ -> Sorted
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


% We found two dependent events, time to update the trace.
update_trace(Event, TraceState, Later, NewOldTrace, State) ->
  #scheduler_state{logger = Logger, optimal = Optimal} = State,
  #trace_state{
     done = [#event{actor = EarlyActor}|Done],
     delay_bound = DelayBound,
     index = EarlyIndex,
     sleeping = Sleeping,
     wakeup_tree = WakeupTree
    } = TraceState,
  
  % Filter non-dependent events.
  NotDep = not_dep(NewOldTrace ++ Later, EarlyActor, EarlyIndex, Event),
  case insert_wakeup(Sleeping ++ Done, WakeupTree, NotDep, Optimal) of
    skip ->
	  %print_debug(yellow, ["SKIP"]),
      ?debug(Logger, "     SKIP~n",[]),
      skip;
	% There is a new wake-up tree.
    NewWakeupTree -> case
        (DelayBound =:= infinity) orelse
        (DelayBound - length(Done ++ WakeupTree) > 0)
      of
        true ->
          trace_plan(Logger, EarlyIndex, NotDep),
          NS = TraceState#trace_state{wakeup_tree = NewWakeupTree},
          [NS|NewOldTrace];
        false ->
          Message =
            "Some interleavings were not considered due to delay bounding.~n",
          ?unique(Logger, ?lwarning, Message, []),
          ?debug(Logger, "     OVER BOUND~n",[]),
          skip
      end
  end.

filter_sleeping([], AvailableActors) -> AvailableActors;
filter_sleeping([#event{actor = Actor}|Sleeping], AvailableActors) ->
  NewAvailableActors =
    case ?is_channel(Actor) of
      true -> lists:keydelete(Actor, 1, AvailableActors);
      false -> lists:delete(Actor, AvailableActors)
    end,
  filter_sleeping(Sleeping, NewAvailableActors).

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

% Go through 'Specials' and for each event add a clock that is
% associated with the message event. AFAIK, this is used to get
% around local delivery issues.
%
%     case Special of
%      {message_received, #Ref} ->
%      {message_delivered, #message_event} ->
%      {message, #message_event} ->
%      {system_communication, user},
%      {new, PID} ->
% Example:ok

% 	ActorClock      -> [{{<0.53.0>,<0.38.0>},4}]
%	Special        -> {message_delivered, #message_event}
%	NewClock        -> [{<0.53.0>,3},{{<0.53.0>,<0.38.0>},4}]
add_pre_message_clocks([], _, Clock) -> Clock;
add_pre_message_clocks([Special|Specials], MessageInfo, Clock) ->
  NewClock =
    case Special of
      {message_received, Id} ->
        case ets:lookup_element(MessageInfo, Id, ?message_delivered) of
          undefined -> Clock;
          RMessageClock -> max_cv(Clock, RMessageClock)
        end;
      {message_delivered, #message_event{message = #message{id = Id}}} ->
        message_clock(Id, MessageInfo, Clock);
      _ -> Clock
    end,
  add_pre_message_clocks(Specials, MessageInfo, NewClock).

message_clock(Id, MessageInfo, ActorClock) ->
  case ets:lookup_element(MessageInfo, Id, ?message_sent) of
    undefined -> ActorClock;
    MessageClock -> max_cv(ActorClock, MessageClock)
  end.

% This function updates the vector clock map for the events
% that are dependent.
% Example:
% Input  -> [{<0.53.0>,8},
%            {<0.62.0>,21},
%            {{<0.38.0>,<0.53.0>},5},
%            {{<0.53.0>,<0.38.0>},4},
%            {{<0.62.0>,<0.38.0>},22}]
% Output  -> [{<0.53.0>,17},
%             {<0.62.0>,21},
%             {{<0.38.0>,<0.53.0>},5},
%             {{<0.53.0>,<0.38.0>},18},
%             {{<0.62.0>,<0.38.0>},22}]

update_clock([], _Event, Clock, _State) ->
  Clock;

update_clock([TraceState|Rest], #event{actor = AC} = Event, Clock, State) ->
  
  #trace_state{
     done = [#event{actor = EarlyActor} = EarlyEvent|_],
     index = EarlyIndex
    } = TraceState,
   
  EarlyClock = lookup_clock_value(EarlyActor, Clock),
  
  %io:format("EarlyEvent     -> ~p~n", [EarlyEvent]),
  %io:format("Event          -> ~p~n", [Event]),

  %io:format("AC             -> ~p~n", [AC]),
  %io:format("EarlyActor     -> ~p~n", [EarlyActor]),
  %io:format("Index Clock    -> ~p ~p~n", [EarlyIndex, EarlyClock]),

  NewClock = case EarlyIndex > EarlyClock of
      false -> Clock;
      true ->
        #scheduler_state{assume_racing = AssumeRacing} = State,
        Dependent =
          concuerror_dependencies:dependent(EarlyEvent, Event, AssumeRacing),
        ?trace(State#scheduler_state.logger,
               "    ~s ~s~n",
               begin
                 Star = fun(false) -> " ";(_) -> "*" end,
                 [Star(Dependent), ?pretty_s(EarlyIndex,EarlyEvent)]
               end),
        case Dependent of
          false -> Clock;
          True when True =:= true; True =:= irreversible ->
            #trace_state{clock_map = ClockMap} = TraceState,
            EarlyActorClock = lookup_clock(EarlyActor, ClockMap),
			%io:format("Dependent    -> ~p~n", [EarlyActorClock]),

            max_cv(
              Clock, orddict:store(EarlyActor, EarlyIndex, EarlyActorClock))
        end
    end,
  
  update_clock(Rest, Event, NewClock, State).

maybe_mark_sent_message(Special, Clock, MessageInfo) when is_list(Special)->
  Message = proplists:lookup(message, Special),
  maybe_mark_sent_message(Message, Clock, MessageInfo);

maybe_mark_sent_message({message, Message}, Clock, MessageInfo) ->
  #message_event{message = #message{id = Id}} = Message,
  ets:update_element(MessageInfo, Id, {?message_sent, Clock});

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
