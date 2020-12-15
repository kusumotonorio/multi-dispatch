USING: combinators formatting kernel math memory mm5 namespaces
prettyprint sequences tools.test tools.time ;
IN: mm5.tests

MIXIN: thing

SINGLETON: paper    INSTANCE: paper thing
SINGLETON: scissors INSTANCE: scissors thing
SINGLETON: rock     INSTANCE: rock thing

SYMBOLS: thing1 thing2 ;


! multi-dispatch
MGENERIC: md-beats? ( obj1 obj2 -- ? )

MM: md-beats? ( :paper :scissors -- ? ) 2drop t ;
MM: md-beats? ( :scissors :rock -- ? ) 2drop t ;
MM: md-beats? ( :rock :paper -- ? ) 2drop t ;
MM: md-beats? ( :thing :thing -- ? ) 2drop f ;

: md-play ( obj1 obj2 -- ? ) md-beats? ;

{ f t f  f f t  t f f 
  f t f  f f t  t f f 
} [ 
    2 [
        paper paper       md-play
        paper scissors    md-play
        paper rock        md-play
        
        scissors paper    md-play
        scissors scissors md-play
        scissors rock     md-play
        
        rock paper        md-play
        rock scissors     md-play
        rock rock         md-play
    ] times
] unit-test


! multi-hook-dispatch
MGENERIC: mhd-beats? ( thing1 thing2 | -- ? )

MM: mhd-beats? ( thing1: paper thing2: scissors | -- ? ) t ; 
MM: mhd-beats? ( thing1: scissors thing2: rock | -- ? ) t ; 
MM: mhd-beats? ( thing1: rock thing2: paper | -- ? ) t ; 
MM: mhd-beats? ( thing1: thing thing2: thing | -- ? ) f ; 

: mhd-play ( -- ? ) mhd-beats? ;

{ f t f  f f t  t f f 
  f t f  f f t  t f f
} [
    2 [
        paper    thing1 set 
        paper    thing2 set mhd-play
        scissors thing2 set mhd-play
        rock     thing2 set mhd-play
    
        scissors thing1 set 
        paper    thing2 set mhd-play
        scissors thing2 set mhd-play
        rock     thing2 set mhd-play
        
        rock     thing1 set 
        paper    thing2 set mhd-play
        scissors thing2 set mhd-play
        rock     thing2 set mhd-play
    ] times
] unit-test 


! sigle-dispach
GENERIC: sd-beats? ( obj1 obj2 -- ? )

M: paper sd-beats? drop rock? [ t ] [ f ] if ; 
M: scissors sd-beats? drop paper? [ t ] [ f ] if ;
M: rock sd-beats? drop scissors? [ t ] [ f ] if ;

: sd-play ( obj1 obj2 -- ? ) sd-beats? ;

{ f t f  f f t  t f f } [ 
    paper paper       sd-play
    paper scissors    sd-play
    paper rock        sd-play
        
    scissors paper    sd-play
    scissors scissors sd-play
    scissors rock     sd-play
    
    rock paper        sd-play
    rock scissors     sd-play
    rock rock         sd-play
] unit-test


! sigle-hook-dispatch
HOOK: shd-beats? thing2 ( -- ? )

M: paper shd-beats? thing1 get rock? [ t ] [ f ] if ; 
M: scissors shd-beats? thing1 get paper? [ t ] [ f ] if ;
M: rock shd-beats? thing1 get scissors? [ t ] [ f ] if ;

: shd-play ( -- ? ) shd-beats? ;

{ f t f  f f t  t f f } [ 
    paper    thing1 set 
    paper    thing2 set shd-play
    scissors thing2 set shd-play
    rock     thing2 set shd-play
    
    scissors thing1 set 
    paper    thing2 set shd-play
    scissors thing2 set shd-play
    rock     thing2 set shd-play
        
    rock     thing1 set 
    paper    thing2 set shd-play
    scissors thing2 set shd-play
    rock     thing2 set shd-play
] unit-test 


! no-dispatch
: beats? ( obj1 obj2 -- ? )
    {
        { rock     [ scissors? [ t ] [ f ] if ] }
        { paper    [ rock?     [ t ] [ f ] if ] }
        { scissors [ paper?    [ t ] [ f ] if ] }
    } case ;

: play ( obj1 obj2 -- ? ) beats? ;

{ f t f  f f t  t f f } [ 
    paper paper       play
    paper scissors    play
    paper rock        play
        
    scissors paper    play
    scissors scissors play
    scissors rock     play
    
    rock paper        play
    rock scissors     play
    rock rock         play
] unit-test


MGENERIC: hook-beats-stack? ( thing1 | thing-s1 thing-s2 -- ? )

MM: hook-beats-stack? ( thing1: paper    | :rock :rock -- ? ) 2drop t ;
MM: hook-beats-stack? ( thing1: scissors | :paper :paper -- ? ) 2drop t ;
MM: hook-beats-stack? ( thing1: rock     | :scissors :scissors -- ? ) 2drop t ;
MM: hook-beats-stack? ( thing1: thing    | :thing :thing -- ? ) 2drop f ;

{ t f } [
    paper thing1 set    rock rock hook-beats-stack?
    scissors thing1 set rock rock hook-beats-stack?    
] unit-test


MGENERIC: hook-beats-stack?-2 ( thing1 thing2 | a: thing1 b: thing2 -- ? )

MM: hook-beats-stack?-2 ( thing1: paper thing2: paper       | a: rock b: rock -- ? ) 2drop t ;
MM: hook-beats-stack?-2 ( thing1: scissors thing2: scissors | a: paper b: paper -- ? ) 2drop t ;
MM: hook-beats-stack?-2 ( thing1: rock thing2: rock         | a: scissors b: scissors -- ? ) 2drop t ;
MM: hook-beats-stack?-2 ( thing1: thing thing2: thing       | a: thing b: thing -- ? ) 2drop f ;

{ t f } [
    paper thing1 set paper thing2 set    rock rock hook-beats-stack?
    scissors thing1 set paper thing2 set rock rock hook-beats-stack?    
] unit-test


MGENERIC: dispatch#1 ( a *b* c -- d )

MM: dispatch#1 ( a: object b: integer c: object -- d ) 3drop "integer" ;
MM: dispatch#1 ( a b: object c -- d ) 3drop "Something other than integer" ;

{ "integer" "Something other than integer" "integer" } [
    1 2 3 dispatch#1
    1 2.0 3 dispatch#1
    1.0 2 3.0 dispatch#1
] unit-test


CONSTANT: TIMES 1000,000
SYMBOL: no-dispatch-time

"\nRepeat all combinations of rock-paper-scissors "

TIMES [
    { [ dup 1,000,000 >= ] [
          [ 1,000,000 / >integer ]
          [ 1,000,000 mod 1,000 / >integer ]
          [ 1,000 mod ] 
          tri "%d,%03d,%03d" sprintf ] }
    { [ dup 1,000 >= ] [
          [ 1,000 / >integer ]
          [ 1,000 mod ] 
          bi "%d,%03d" sprintf
      ] }
    [ "%d" sprintf ]
] cond
" times\n" 3append printf

gc
[
    TIMES [
        paper paper       play drop
        paper scissors    play drop
        paper rock        play drop
        
        scissors paper    play drop
        scissors scissors play drop
        scissors rock     play drop
        
        rock paper        play drop
        rock scissors     play drop
        rock rock         play drop
    ] times
] benchmark dup no-dispatch-time set
1.0e9 / "no-dispatch:          %.6f seconds (reference)\n" printf

gc
[
    TIMES [
        paper paper       sd-play drop
        paper scissors    sd-play drop
        paper rock        sd-play drop
        
        scissors paper    sd-play drop
        scissors scissors sd-play drop
        scissors rock     sd-play drop
        
        rock paper        sd-play drop
        rock scissors     sd-play drop
        rock rock         sd-play drop
    ] times
] benchmark
[ 1.0e9 / ] [ no-dispatch-time get / ] bi
"single-dispatch:      %.6f seconds (%.2f times slower)\n" printf

gc
[
    TIMES [
        paper paper       md-play drop
        paper scissors    md-play drop
        paper rock        md-play drop
        
        scissors paper    md-play drop
        scissors scissors md-play drop
        scissors rock     md-play drop
        
        rock paper        md-play drop
        rock scissors     md-play drop
        rock rock         md-play drop
    ] times
] benchmark
[ 1.0e9 / ] [ no-dispatch-time get / ] bi
"multi-dispatch:       %.6f seconds (%.2f times slower)\n" printf

gc
[
    TIMES [
        paper paper       md-play drop
        paper paper       md-play drop
        paper paper       md-play drop
        paper paper       md-play drop
        paper paper       md-play drop
        paper paper       md-play drop
        paper paper       md-play drop
        paper paper       md-play drop
        paper paper       md-play drop        
    ] times
] benchmark
[ 1.0e9 / ] [ no-dispatch-time get / ] bi
"multi-dispatch2:      %.6f seconds (%.2f times slower)\n" printf

gc
[
    TIMES [
        paper    thing1 set 
        paper    thing2 set shd-play drop
        scissors thing2 set shd-play drop
        rock     thing2 set shd-play drop
        
        scissors thing1 set 
        paper    thing2 set shd-play drop
        scissors thing2 set shd-play drop
        rock     thing2 set shd-play drop
        
        rock     thing1 set 
        paper    thing2 set shd-play drop
        scissors thing2 set shd-play drop
        rock     thing2 set shd-play drop
    ] times
] benchmark
[ 1.0e9 / ] [ no-dispatch-time get / ] bi
"single-hook-dispatch: %.6f seconds (%.2f times slower)\n" printf

gc
[
    TIMES [
        paper    thing1 set 
        paper    thing2 set mhd-play drop
        scissors thing2 set mhd-play drop
        rock     thing2 set mhd-play drop
        
        scissors thing1 set 
        paper    thing2 set mhd-play drop
        scissors thing2 set mhd-play drop
        rock     thing2 set mhd-play drop
        
        rock     thing1 set 
        paper    thing2 set mhd-play drop
        scissors thing2 set mhd-play drop
        rock     thing2 set mhd-play drop
    ] times
] benchmark
[ 1.0e9 / ] [ no-dispatch-time get / ] bi
"multi-hook-dispatch:  %.6f seconds (%.2f times slower)\n" printf


SYMBOL: ref

MIXIN: man

MGENERIC: ln-beats? ( man man -- ? )

MM: ln-beats? ( :man :man -- ? ) 2drop f ;
SINGLETON: the-man-No.001 INSTANCE: the-man-No.001 man   MM: ln-beats? ( :man :the-man-No.001 -- ? ) 2drop t ;
SINGLETON: the-man-No.002 INSTANCE: the-man-No.002 man   MM: ln-beats? ( :man :the-man-No.002 -- ? ) 2drop t ;
SINGLETON: the-man-No.003 INSTANCE: the-man-No.003 man   MM: ln-beats? ( :man :the-man-No.003 -- ? ) 2drop t ;
SINGLETON: the-man-No.004 INSTANCE: the-man-No.004 man   MM: ln-beats? ( :man :the-man-No.004 -- ? ) 2drop t ;
SINGLETON: the-man-No.005 INSTANCE: the-man-No.005 man   MM: ln-beats? ( :man :the-man-No.005 -- ? ) 2drop t ;
SINGLETON: the-man-No.006 INSTANCE: the-man-No.006 man   MM: ln-beats? ( :man :the-man-No.006 -- ? ) 2drop t ;
SINGLETON: the-man-No.007 INSTANCE: the-man-No.007 man   MM: ln-beats? ( :man :the-man-No.007 -- ? ) 2drop t ;
SINGLETON: the-man-No.008 INSTANCE: the-man-No.008 man   MM: ln-beats? ( :man :the-man-No.008 -- ? ) 2drop t ;
SINGLETON: the-man-No.009 INSTANCE: the-man-No.009 man   MM: ln-beats? ( :man :the-man-No.009 -- ? ) 2drop t ;
SINGLETON: the-man-No.010 INSTANCE: the-man-No.010 man   MM: ln-beats? ( :man :the-man-No.010 -- ? ) 2drop t ;
SINGLETON: the-man-No.011 INSTANCE: the-man-No.011 man   MM: ln-beats? ( :man :the-man-No.011 -- ? ) 2drop t ;
SINGLETON: the-man-No.012 INSTANCE: the-man-No.012 man   MM: ln-beats? ( :man :the-man-No.012 -- ? ) 2drop t ;
SINGLETON: the-man-No.013 INSTANCE: the-man-No.013 man   MM: ln-beats? ( :man :the-man-No.013 -- ? ) 2drop t ;
SINGLETON: the-man-No.014 INSTANCE: the-man-No.014 man   MM: ln-beats? ( :man :the-man-No.014 -- ? ) 2drop t ;
SINGLETON: the-man-No.015 INSTANCE: the-man-No.015 man   MM: ln-beats? ( :man :the-man-No.015 -- ? ) 2drop t ;
SINGLETON: the-man-No.016 INSTANCE: the-man-No.016 man   MM: ln-beats? ( :man :the-man-No.016 -- ? ) 2drop t ;
SINGLETON: the-man-No.017 INSTANCE: the-man-No.017 man   MM: ln-beats? ( :man :the-man-No.017 -- ? ) 2drop t ;
SINGLETON: the-man-No.018 INSTANCE: the-man-No.018 man   MM: ln-beats? ( :man :the-man-No.018 -- ? ) 2drop t ;
SINGLETON: the-man-No.019 INSTANCE: the-man-No.019 man   MM: ln-beats? ( :man :the-man-No.019 -- ? ) 2drop t ;
SINGLETON: the-man-No.020 INSTANCE: the-man-No.020 man   MM: ln-beats? ( :man :the-man-No.020 -- ? ) 2drop t ;
SINGLETON: the-man-No.021 INSTANCE: the-man-No.021 man   MM: ln-beats? ( :man :the-man-No.021 -- ? ) 2drop t ;
SINGLETON: the-man-No.022 INSTANCE: the-man-No.022 man   MM: ln-beats? ( :man :the-man-No.022 -- ? ) 2drop t ;
SINGLETON: the-man-No.023 INSTANCE: the-man-No.023 man   MM: ln-beats? ( :man :the-man-No.023 -- ? ) 2drop t ;
SINGLETON: the-man-No.024 INSTANCE: the-man-No.024 man   MM: ln-beats? ( :man :the-man-No.024 -- ? ) 2drop t ;
SINGLETON: the-man-No.025 INSTANCE: the-man-No.025 man   MM: ln-beats? ( :man :the-man-No.025 -- ? ) 2drop t ;
SINGLETON: the-man-No.026 INSTANCE: the-man-No.026 man   MM: ln-beats? ( :man :the-man-No.026 -- ? ) 2drop t ;
SINGLETON: the-man-No.027 INSTANCE: the-man-No.027 man   MM: ln-beats? ( :man :the-man-No.027 -- ? ) 2drop t ;
SINGLETON: the-man-No.028 INSTANCE: the-man-No.028 man   MM: ln-beats? ( :man :the-man-No.028 -- ? ) 2drop t ;
SINGLETON: the-man-No.029 INSTANCE: the-man-No.029 man   MM: ln-beats? ( :man :the-man-No.029 -- ? ) 2drop t ;
SINGLETON: the-man-No.030 INSTANCE: the-man-No.030 man   MM: ln-beats? ( :man :the-man-No.030 -- ? ) 2drop t ;
SINGLETON: the-man-No.031 INSTANCE: the-man-No.031 man   MM: ln-beats? ( :man :the-man-No.031 -- ? ) 2drop t ;
SINGLETON: the-man-No.032 INSTANCE: the-man-No.032 man   MM: ln-beats? ( :man :the-man-No.032 -- ? ) 2drop t ;
SINGLETON: the-man-No.033 INSTANCE: the-man-No.033 man   MM: ln-beats? ( :man :the-man-No.033 -- ? ) 2drop t ;
SINGLETON: the-man-No.034 INSTANCE: the-man-No.034 man   MM: ln-beats? ( :man :the-man-No.034 -- ? ) 2drop t ;
SINGLETON: the-man-No.035 INSTANCE: the-man-No.035 man   MM: ln-beats? ( :man :the-man-No.035 -- ? ) 2drop t ;
SINGLETON: the-man-No.036 INSTANCE: the-man-No.036 man   MM: ln-beats? ( :man :the-man-No.036 -- ? ) 2drop t ;
SINGLETON: the-man-No.037 INSTANCE: the-man-No.037 man   MM: ln-beats? ( :man :the-man-No.037 -- ? ) 2drop t ;
SINGLETON: the-man-No.038 INSTANCE: the-man-No.038 man   MM: ln-beats? ( :man :the-man-No.038 -- ? ) 2drop t ;
SINGLETON: the-man-No.039 INSTANCE: the-man-No.039 man   MM: ln-beats? ( :man :the-man-No.039 -- ? ) 2drop t ;
SINGLETON: the-man-No.040 INSTANCE: the-man-No.040 man   MM: ln-beats? ( :man :the-man-No.040 -- ? ) 2drop t ;
SINGLETON: the-man-No.041 INSTANCE: the-man-No.041 man   MM: ln-beats? ( :man :the-man-No.041 -- ? ) 2drop t ;
SINGLETON: the-man-No.042 INSTANCE: the-man-No.042 man   MM: ln-beats? ( :man :the-man-No.042 -- ? ) 2drop t ;
SINGLETON: the-man-No.043 INSTANCE: the-man-No.043 man   MM: ln-beats? ( :man :the-man-No.043 -- ? ) 2drop t ;
SINGLETON: the-man-No.044 INSTANCE: the-man-No.044 man   MM: ln-beats? ( :man :the-man-No.044 -- ? ) 2drop t ;
SINGLETON: the-man-No.045 INSTANCE: the-man-No.045 man   MM: ln-beats? ( :man :the-man-No.045 -- ? ) 2drop t ;
SINGLETON: the-man-No.046 INSTANCE: the-man-No.046 man   MM: ln-beats? ( :man :the-man-No.046 -- ? ) 2drop t ;
SINGLETON: the-man-No.047 INSTANCE: the-man-No.047 man   MM: ln-beats? ( :man :the-man-No.047 -- ? ) 2drop t ;
SINGLETON: the-man-No.048 INSTANCE: the-man-No.048 man   MM: ln-beats? ( :man :the-man-No.048 -- ? ) 2drop t ;
SINGLETON: the-man-No.049 INSTANCE: the-man-No.049 man   MM: ln-beats? ( :man :the-man-No.049 -- ? ) 2drop t ;
SINGLETON: the-man-No.050 INSTANCE: the-man-No.050 man   MM: ln-beats? ( :man :the-man-No.050 -- ? ) 2drop t ;
SINGLETON: the-man-No.051 INSTANCE: the-man-No.051 man   MM: ln-beats? ( :man :the-man-No.051 -- ? ) 2drop t ;
SINGLETON: the-man-No.052 INSTANCE: the-man-No.052 man   MM: ln-beats? ( :man :the-man-No.052 -- ? ) 2drop t ;
SINGLETON: the-man-No.053 INSTANCE: the-man-No.053 man   MM: ln-beats? ( :man :the-man-No.053 -- ? ) 2drop t ;
SINGLETON: the-man-No.054 INSTANCE: the-man-No.054 man   MM: ln-beats? ( :man :the-man-No.054 -- ? ) 2drop t ;
SINGLETON: the-man-No.055 INSTANCE: the-man-No.055 man   MM: ln-beats? ( :man :the-man-No.055 -- ? ) 2drop t ;
SINGLETON: the-man-No.056 INSTANCE: the-man-No.056 man   MM: ln-beats? ( :man :the-man-No.056 -- ? ) 2drop t ;
SINGLETON: the-man-No.057 INSTANCE: the-man-No.057 man   MM: ln-beats? ( :man :the-man-No.057 -- ? ) 2drop t ;
SINGLETON: the-man-No.058 INSTANCE: the-man-No.058 man   MM: ln-beats? ( :man :the-man-No.058 -- ? ) 2drop t ;
SINGLETON: the-man-No.059 INSTANCE: the-man-No.059 man   MM: ln-beats? ( :man :the-man-No.059 -- ? ) 2drop t ;
SINGLETON: the-man-No.060 INSTANCE: the-man-No.060 man   MM: ln-beats? ( :man :the-man-No.060 -- ? ) 2drop t ;
SINGLETON: the-man-No.061 INSTANCE: the-man-No.061 man   MM: ln-beats? ( :man :the-man-No.061 -- ? ) 2drop t ;
SINGLETON: the-man-No.062 INSTANCE: the-man-No.062 man   MM: ln-beats? ( :man :the-man-No.062 -- ? ) 2drop t ;
SINGLETON: the-man-No.063 INSTANCE: the-man-No.063 man   MM: ln-beats? ( :man :the-man-No.063 -- ? ) 2drop t ;
SINGLETON: the-man-No.064 INSTANCE: the-man-No.064 man   MM: ln-beats? ( :man :the-man-No.064 -- ? ) 2drop t ;
SINGLETON: the-man-No.065 INSTANCE: the-man-No.065 man   MM: ln-beats? ( :man :the-man-No.065 -- ? ) 2drop t ;
SINGLETON: the-man-No.066 INSTANCE: the-man-No.066 man   MM: ln-beats? ( :man :the-man-No.066 -- ? ) 2drop t ;
SINGLETON: the-man-No.067 INSTANCE: the-man-No.067 man   MM: ln-beats? ( :man :the-man-No.067 -- ? ) 2drop t ;
SINGLETON: the-man-No.068 INSTANCE: the-man-No.068 man   MM: ln-beats? ( :man :the-man-No.068 -- ? ) 2drop t ;
SINGLETON: the-man-No.069 INSTANCE: the-man-No.069 man   MM: ln-beats? ( :man :the-man-No.069 -- ? ) 2drop t ;
SINGLETON: the-man-No.070 INSTANCE: the-man-No.070 man   MM: ln-beats? ( :man :the-man-No.070 -- ? ) 2drop t ;
SINGLETON: the-man-No.071 INSTANCE: the-man-No.071 man   MM: ln-beats? ( :man :the-man-No.071 -- ? ) 2drop t ;
SINGLETON: the-man-No.072 INSTANCE: the-man-No.072 man   MM: ln-beats? ( :man :the-man-No.072 -- ? ) 2drop t ;
SINGLETON: the-man-No.073 INSTANCE: the-man-No.073 man   MM: ln-beats? ( :man :the-man-No.073 -- ? ) 2drop t ;
SINGLETON: the-man-No.074 INSTANCE: the-man-No.074 man   MM: ln-beats? ( :man :the-man-No.074 -- ? ) 2drop t ;
SINGLETON: the-man-No.075 INSTANCE: the-man-No.075 man   MM: ln-beats? ( :man :the-man-No.075 -- ? ) 2drop t ;
SINGLETON: the-man-No.076 INSTANCE: the-man-No.076 man   MM: ln-beats? ( :man :the-man-No.076 -- ? ) 2drop t ;
SINGLETON: the-man-No.077 INSTANCE: the-man-No.077 man   MM: ln-beats? ( :man :the-man-No.077 -- ? ) 2drop t ;
SINGLETON: the-man-No.078 INSTANCE: the-man-No.078 man   MM: ln-beats? ( :man :the-man-No.078 -- ? ) 2drop t ;
SINGLETON: the-man-No.079 INSTANCE: the-man-No.079 man   MM: ln-beats? ( :man :the-man-No.079 -- ? ) 2drop t ;
SINGLETON: the-man-No.080 INSTANCE: the-man-No.080 man   MM: ln-beats? ( :man :the-man-No.080 -- ? ) 2drop t ;
SINGLETON: the-man-No.081 INSTANCE: the-man-No.081 man   MM: ln-beats? ( :man :the-man-No.081 -- ? ) 2drop t ;
SINGLETON: the-man-No.082 INSTANCE: the-man-No.082 man   MM: ln-beats? ( :man :the-man-No.082 -- ? ) 2drop t ;
SINGLETON: the-man-No.083 INSTANCE: the-man-No.083 man   MM: ln-beats? ( :man :the-man-No.083 -- ? ) 2drop t ;
SINGLETON: the-man-No.084 INSTANCE: the-man-No.084 man   MM: ln-beats? ( :man :the-man-No.084 -- ? ) 2drop t ;
SINGLETON: the-man-No.085 INSTANCE: the-man-No.085 man   MM: ln-beats? ( :man :the-man-No.085 -- ? ) 2drop t ;
SINGLETON: the-man-No.086 INSTANCE: the-man-No.086 man   MM: ln-beats? ( :man :the-man-No.086 -- ? ) 2drop t ;
SINGLETON: the-man-No.087 INSTANCE: the-man-No.087 man   MM: ln-beats? ( :man :the-man-No.087 -- ? ) 2drop t ;
SINGLETON: the-man-No.088 INSTANCE: the-man-No.088 man   MM: ln-beats? ( :man :the-man-No.088 -- ? ) 2drop t ;
SINGLETON: the-man-No.089 INSTANCE: the-man-No.089 man   MM: ln-beats? ( :man :the-man-No.089 -- ? ) 2drop t ;
SINGLETON: the-man-No.090 INSTANCE: the-man-No.090 man   MM: ln-beats? ( :man :the-man-No.090 -- ? ) 2drop t ;
SINGLETON: the-man-No.091 INSTANCE: the-man-No.091 man   MM: ln-beats? ( :man :the-man-No.091 -- ? ) 2drop t ;
SINGLETON: the-man-No.092 INSTANCE: the-man-No.092 man   MM: ln-beats? ( :man :the-man-No.092 -- ? ) 2drop t ;
SINGLETON: the-man-No.093 INSTANCE: the-man-No.093 man   MM: ln-beats? ( :man :the-man-No.093 -- ? ) 2drop t ;
SINGLETON: the-man-No.094 INSTANCE: the-man-No.094 man   MM: ln-beats? ( :man :the-man-No.094 -- ? ) 2drop t ;
SINGLETON: the-man-No.095 INSTANCE: the-man-No.095 man   MM: ln-beats? ( :man :the-man-No.095 -- ? ) 2drop t ;
SINGLETON: the-man-No.096 INSTANCE: the-man-No.096 man   MM: ln-beats? ( :man :the-man-No.096 -- ? ) 2drop t ;
SINGLETON: the-man-No.097 INSTANCE: the-man-No.097 man   MM: ln-beats? ( :man :the-man-No.097 -- ? ) 2drop t ;
SINGLETON: the-man-No.098 INSTANCE: the-man-No.098 man   MM: ln-beats? ( :man :the-man-No.098 -- ? ) 2drop t ;
SINGLETON: the-man-No.099 INSTANCE: the-man-No.099 man   MM: ln-beats? ( :man :the-man-No.099 -- ? ) 2drop t ;
SINGLETON: the-man-No.100 INSTANCE: the-man-No.100 man   MM: ln-beats? ( :man :the-man-No.100 -- ? ) 2drop t ;
SINGLETON: the-man-No.101 INSTANCE: the-man-No.101 man   MM: ln-beats? ( :man :the-man-No.101 -- ? ) 2drop t ;
SINGLETON: the-man-No.102 INSTANCE: the-man-No.102 man   MM: ln-beats? ( :man :the-man-No.102 -- ? ) 2drop t ;
SINGLETON: the-man-No.103 INSTANCE: the-man-No.103 man   MM: ln-beats? ( :man :the-man-No.103 -- ? ) 2drop t ;
SINGLETON: the-man-No.104 INSTANCE: the-man-No.104 man   MM: ln-beats? ( :man :the-man-No.104 -- ? ) 2drop t ;
SINGLETON: the-man-No.105 INSTANCE: the-man-No.105 man   MM: ln-beats? ( :man :the-man-No.105 -- ? ) 2drop t ;
SINGLETON: the-man-No.106 INSTANCE: the-man-No.106 man   MM: ln-beats? ( :man :the-man-No.106 -- ? ) 2drop t ;
SINGLETON: the-man-No.107 INSTANCE: the-man-No.107 man   MM: ln-beats? ( :man :the-man-No.107 -- ? ) 2drop t ;
SINGLETON: the-man-No.108 INSTANCE: the-man-No.108 man   MM: ln-beats? ( :man :the-man-No.108 -- ? ) 2drop t ;
SINGLETON: the-man-No.109 INSTANCE: the-man-No.109 man   MM: ln-beats? ( :man :the-man-No.109 -- ? ) 2drop t ;
SINGLETON: the-man-No.110 INSTANCE: the-man-No.110 man   MM: ln-beats? ( :man :the-man-No.110 -- ? ) 2drop t ;
SINGLETON: the-man-No.111 INSTANCE: the-man-No.111 man   MM: ln-beats? ( :man :the-man-No.111 -- ? ) 2drop t ;
SINGLETON: the-man-No.112 INSTANCE: the-man-No.112 man   MM: ln-beats? ( :man :the-man-No.112 -- ? ) 2drop t ;
SINGLETON: the-man-No.113 INSTANCE: the-man-No.113 man   MM: ln-beats? ( :man :the-man-No.113 -- ? ) 2drop t ;
SINGLETON: the-man-No.114 INSTANCE: the-man-No.114 man   MM: ln-beats? ( :man :the-man-No.114 -- ? ) 2drop t ;
SINGLETON: the-man-No.115 INSTANCE: the-man-No.115 man   MM: ln-beats? ( :man :the-man-No.115 -- ? ) 2drop t ;
SINGLETON: the-man-No.116 INSTANCE: the-man-No.116 man   MM: ln-beats? ( :man :the-man-No.116 -- ? ) 2drop t ;
SINGLETON: the-man-No.117 INSTANCE: the-man-No.117 man   MM: ln-beats? ( :man :the-man-No.117 -- ? ) 2drop t ;
SINGLETON: the-man-No.118 INSTANCE: the-man-No.118 man   MM: ln-beats? ( :man :the-man-No.118 -- ? ) 2drop t ;
SINGLETON: the-man-No.119 INSTANCE: the-man-No.119 man   MM: ln-beats? ( :man :the-man-No.119 -- ? ) 2drop t ;
SINGLETON: the-man-No.120 INSTANCE: the-man-No.120 man   MM: ln-beats? ( :man :the-man-No.120 -- ? ) 2drop t ;

{ t t t t } [
    the-man-No.119 the-man-No.120 ln-beats?
    the-man-No.120 the-man-No.119 ln-beats?
    the-man-No.001 the-man-No.002 ln-beats?
    the-man-No.002 the-man-No.001 ln-beats?
] unit-test

"\nRepeat showdown between the two "
TIMES [
    { [ dup 1,000,000 >= ] [
          [ 1,000,000 / >integer ]
          [ 1,000,000 mod 1,000 / >integer ]
          [ 1,000 mod ] 
          tri "%d,%03d,%03d" sprintf ] }
    { [ dup 1,000 >= ] [
          [ 1,000 / >integer ]
          [ 1,000 mod ] 
          bi "%d,%03d" sprintf
      ] }
    [ "%d" sprintf ]
] cond
" * 9 times\n" 3append printf

gc
[
    TIMES [
        the-man-No.067 the-man-No.066 ln-beats? drop
        the-man-No.067 the-man-No.066 ln-beats? drop
        the-man-No.067 the-man-No.066 ln-beats? drop

        the-man-No.067 the-man-No.066 ln-beats? drop
        the-man-No.067 the-man-No.066 ln-beats? drop
        the-man-No.067 the-man-No.066 ln-beats? drop

        the-man-No.067 the-man-No.066 ln-beats? drop
        the-man-No.067 the-man-No.066 ln-beats? drop
        the-man-No.067 the-man-No.066 ln-beats? drop

    ] times
] benchmark dup ref set
1.0e9 / "No.067 vs. No.066: %.6f　seconds\n" printf

gc
[
    TIMES [
        the-man-No.072 the-man-No.074 ln-beats? drop
        the-man-No.072 the-man-No.074 ln-beats? drop
        the-man-No.072 the-man-No.074 ln-beats? drop

        the-man-No.072 the-man-No.074 ln-beats? drop
        the-man-No.072 the-man-No.074 ln-beats? drop
        the-man-No.072 the-man-No.074 ln-beats? drop

        the-man-No.072 the-man-No.074 ln-beats? drop
        the-man-No.072 the-man-No.074 ln-beats? drop
        the-man-No.072 the-man-No.074 ln-beats? drop
    ] times
] benchmark
[ 1.0e9 / ] [ ref get / ] bi
"No.072 vs. No.074: %.6f　seconds (%.2f times slower)\n" printf
