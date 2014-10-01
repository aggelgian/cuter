%% -*- erlang-indent-level: 2 -*-
%%------------------------------------------------------------------------------
-module(cuter_json_tests).

-include_lib("eunit/include/eunit.hrl").
-include("eunit_config.hrl").

-spec test() -> ok | {error | term()}. %% Silence dialyzer warning

%% Encoding / Decoding tests
-spec encdec_test_() -> term().
encdec_test_() ->
  Ts = [
    {"Integers", [
      {"Positive", 42},
      {"Negative", -42}
    ]},
    {"Floats", [
      {"Positive", 3.14},
      {"Negative", -42.42}
    ]},
    {"Atoms", [
      {"Simple", ok},
      {"With Special Characters", '_@#$@#4f'}
    ]},
    {"Lists", [
      {"Empty", []},
      {"Simple", [1,2,3]},
      {"With shared subterms", [1,2,[1,2],[3,1,2]] },
      {"Random alphanumeric string", binary_to_list(base64:encode(crypto:strong_rand_bytes(42)))}
    ]},
    {"Tuples", [
      {"Empty", {}},
      {"Simple", {1,2,3}},
      {"With shared subterms", {1,2,{1,2},{3,1,2},{1,2}}}
    ]},
    {"Symbolic Variables", [
      {"Simple", cuter_symbolic:fresh_symbolic_var()}
    ]},
    {"Mixed", [
      {"I", {[1,2],[1,2],{[1,2],[1,2]}}},
      {"II", [1,ok,{4,1},[4,4.5],4,4.5]},
      {"III", {2.23, true, [2, 3, {234, 34, false}], {ok, fail, 424242}}}
    ]}
  ],
  Setup = fun(T) -> fun() -> T end end,
  Inst = fun encode_decode/1,
  [{"JSON Encoding / Decoding: " ++ C, {setup, Setup(T), Inst}} || {C, T} <- Ts].

%% Encoding unsupported terms tests
encode_decode(Terms) ->
  Enc = fun cuter_json:term_to_json/1,
  Dec = fun cuter_json:json_to_term/1,
  [{Descr, ?_assertEqual(T, Dec(Enc(T)))} || {Descr, T} <- Terms].


-spec enc_fail_test_() -> term().
enc_fail_test_() ->
  Enc = fun cuter_json:term_to_json/1,
  Ts = [
    {"Pid", self()},
    {"Reference", make_ref()},
    {"Binary", <<42>>},
    {"Map", #{ok=>42}},
    {"Fun", fun() -> ok end}
  ],
  {"JSON Encoding Fail", [{Dsr, ?_assertThrow({unsupported_term, _}, Enc(T))} || {Dsr, T} <- Ts]}.



