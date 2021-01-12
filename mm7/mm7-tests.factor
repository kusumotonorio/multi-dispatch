USING: arrays combinators formatting kernel math math.ranges
memory mm7 namespaces prettyprint quotations sequences
tools.test tools.time ;
IN: mm7.tests

MIXIN: thing

SINGLETON: paper    INSTANCE: paper thing
SINGLETON: scissors INSTANCE: scissors thing
SINGLETON: rock     INSTANCE: rock thing

SYMBOLS: thing1 thing2 ;


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


! multi-dispatch
MGENERIC: md-beats? ( obj1 obj2 -- ? )

MM:: md-beats? ( obj1: paper obj2: scissors -- ? ) obj1 obj2 2drop t ;
MM:: md-beats? ( :scissors :rock -- ? ) t ;
MM:: md-beats? ( :rock :paper -- ? ) t ;
MM:: md-beats? ( :thing :thing -- ? ) f ;

: md-play ( obj1 obj2 -- ? ) md-beats? ;

{ f t f  f f t  t f f } [ 
    paper paper       md-play
    paper scissors    md-play
    paper rock        md-play
    
    scissors paper    md-play
    scissors scissors md-play
    scissors rock     md-play
    
    rock paper        md-play
    rock scissors     md-play
    rock rock         md-play
] unit-test


! multi-hook-dispatch
MGENERIC: mhd-beats? ( thing1 thing2 | -- ? )

MM: mhd-beats? ( thing1: paper thing2: scissors | -- ? ) t ; 
MM: mhd-beats? ( thing1: scissors thing2: rock | -- ? ) t ; 
MM: mhd-beats? ( thing1: rock thing2: paper | -- ? ) t ; 
MM: mhd-beats? ( thing1: thing thing2: thing | -- ? ) f ; 

: mhd-play ( -- ? ) mhd-beats? ;

{ f t f  f f t  t f f } [
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

! multi-sigle-dispach
MGENERIC: smd-beats? ( obj1 obj2 -- ? )

MM: smd-beats? ( obj1 obj2: paper -- ? )    drop rock? [ t ] [ f ] if ; 
MM: smd-beats? ( obj1 obj2: scissors -- ? ) drop paper? [ t ] [ f ] if ;
MM: smd-beats? ( obj1 obj2: rock -- ? )     drop scissors? [ t ] [ f ] if ;

: smd-play ( obj1 obj2 -- ? ) smd-beats? ;

{ 
    f t f  f f t  t f f 
    f t f  f f t  t f f 
} [
    2 [
        paper paper       smd-play
        paper scissors    smd-play
        paper rock        smd-play
        
        scissors paper    smd-play
        scissors scissors smd-play
        scissors rock     smd-play
        
        rock paper        smd-play
        rock scissors     smd-play
        rock rock         smd-play
    ] times
] unit-test

{ 
    f t f  f f t  t f f 
    f t f  f f t  t f f 
} [
    2 [
        paper paper       smd-play
        paper scissors    smd-play
        paper rock        smd-play
        
        scissors paper    smd-play
        scissors scissors smd-play
        scissors rock     smd-play
        
        rock paper        smd-play
        rock scissors     smd-play
        rock rock         smd-play
    ] times
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

! sigle-spac-hook-multi-dispatch
MGENERIC: shmd-beats? ( thing2 | -- ? )

MM: shmd-beats? ( thing2: scissors | -- ? ) thing1 get paper? [ t ] [ f ] if ; 
MM: shmd-beats? ( thing2: rock | -- ? ) thing1 get scissors? [ t ] [ f ] if ; 
MM: shmd-beats? ( thing2: paper | -- ? ) thing1 get rock? [ t ] [ f ] if ; 

: shmd-play ( -- ? ) shd-beats? ;

{ f t f  f f t  t f f } [ 
    paper    thing1 set 
    paper    thing2 set shmd-play
    scissors thing2 set shmd-play
    rock     thing2 set shmd-play
    
    scissors thing1 set 
    paper    thing2 set shmd-play
    scissors thing2 set shmd-play
    rock     thing2 set shmd-play
        
    rock     thing1 set 
    paper    thing2 set shmd-play
    scissors thing2 set shmd-play
    rock     thing2 set shmd-play
] unit-test 


MGENERIC: hook-beats-stack? ( thing1 | thing-s1 thing-s2 -- ? )

MM: hook-beats-stack? ( thing1: paper    | :rock :rock -- ? )
    2drop t ;

MM: hook-beats-stack? ( thing1: scissors | :paper :paper -- ? )
    2drop t ;

MM: hook-beats-stack? ( thing1: rock     | :scissors :scissors -- ? )
    2drop t ;

MM: hook-beats-stack? ( thing1: thing    | :thing :thing -- ? )
    2drop f ;

{ t f } [
    paper thing1 set    rock rock hook-beats-stack?
    scissors thing1 set rock rock hook-beats-stack?    
] unit-test


MGENERIC: hook-beats-stack?-2 ( thing1 thing2 | a: thing1 b: thing2 -- ? )

MM: hook-beats-stack?-2 ( thing1: paper thing2: paper | a: rock b: rock -- ? )
    2drop t ;

MM: hook-beats-stack?-2 ( thing1: scissors thing2: scissors |
                          a: paper b: paper -- ? )
    2drop t ;

MM: hook-beats-stack?-2 ( thing1: rock thing2: rock |
                          a: scissors b: scissors -- ? )
    2drop t ;

MM: hook-beats-stack?-2 ( thing1: thing thing2: thing |
                          a: thing b: thing -- ? )
    2drop f ;

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


CONSTANT: TIMES 100,000
SYMBOL: no-dispatch-time

"\n"
TIMES [
    { [ dup 1,000,000 >= ] [
          [ 1,000,000 / >integer ]
          [ 1,000,000 mod 1,000 / >integer ]
          [ 1,000 mod ] 
          tri "%d,%03d,%03d" sprintf ] }
    { [ dup 1,000 >= ] [
          [ 1,000 / >integer ]
          [ 1,000 mod ] 
          bi "%d,%03d" sprintf ] }
    [ "%d" sprintf ]
] cond
" repetitions of all combinations of rock-paper-scissors\n" 3append printf

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
1.0e9 / 
"no-dispatch:                %.6f seconds (reference)\n" printf

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
"single-dispatch:            %.6f seconds (%.2f times slower)\n" printf

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
"multi-dispatch:             %.6f seconds (%.2f times slower)\n" printf

gc
[
    TIMES [
        paper paper       smd-play drop
        paper scissors    smd-play drop
        paper rock        smd-play drop
        
        scissors paper    smd-play drop
        scissors scissors smd-play drop
        scissors rock     smd-play drop
        
        rock paper        smd-play drop
        rock scissors     smd-play drop
        rock rock         smd-play drop
    ] times
] benchmark
[ 1.0e9 / ] [ no-dispatch-time get / ] bi
"single spec multi-dispatch: %.6f seconds (%.2f times slower)\n" printf

gc
[
    TIMES [
        paper    thing1 set 
        paper    thing2 set shd-play drop
        scissors thing2 set shd-play drop
        rock     thing2 set shd-play drop
        
        scissors thing1 set paper thing2 set shd-play drop scissors
        thing2 set shd-play drop rock thing2 set shd-play drop
        
        rock     thing1 set 
        paper    thing2 set shd-play drop
        scissors thing2 set shd-play drop
        rock     thing2 set shd-play drop
    ] times
] benchmark
[ 1.0e9 / ] [ no-dispatch-time get / ] bi
"single-hook-dispatch:       %.6f seconds (%.2f times slower)\n" printf

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
"multi-hook-dispatch:        %.6f seconds (%.2f times slower)\n" printf

gc
[
    TIMES [
        paper    thing1 set 
        paper    thing2 set shmd-play drop
        scissors thing2 set shmd-play drop
        rock     thing2 set shmd-play drop
        
        scissors thing1 set paper thing2 set shd-play drop scissors
        thing2 set shd-play drop rock thing2 set shd-play drop
        
        rock     thing1 set 
        paper    thing2 set shmd-play drop
        scissors thing2 set shmd-play drop
        rock     thing2 set shmd-play drop
    ] times
] benchmark
[ 1.0e9 / ] [ no-dispatch-time get / ] bi
"single-hook-multi-dispatch: %.6f seconds (%.2f times slower)\n" printf


SYMBOL: ref

MIXIN: man

SINGLETON: the-man-No.001 INSTANCE: the-man-No.001 man
SINGLETON: the-man-No.002 INSTANCE: the-man-No.002 man
SINGLETON: the-man-No.003 INSTANCE: the-man-No.003 man
SINGLETON: the-man-No.004 INSTANCE: the-man-No.004 man
SINGLETON: the-man-No.005 INSTANCE: the-man-No.005 man
SINGLETON: the-man-No.006 INSTANCE: the-man-No.006 man
SINGLETON: the-man-No.007 INSTANCE: the-man-No.007 man
SINGLETON: the-man-No.008 INSTANCE: the-man-No.008 man
SINGLETON: the-man-No.009 INSTANCE: the-man-No.009 man
SINGLETON: the-man-No.010 INSTANCE: the-man-No.010 man
SINGLETON: the-man-No.011 INSTANCE: the-man-No.011 man
SINGLETON: the-man-No.012 INSTANCE: the-man-No.012 man
SINGLETON: the-man-No.013 INSTANCE: the-man-No.013 man
SINGLETON: the-man-No.014 INSTANCE: the-man-No.014 man
SINGLETON: the-man-No.015 INSTANCE: the-man-No.015 man
SINGLETON: the-man-No.016 INSTANCE: the-man-No.016 man
SINGLETON: the-man-No.017 INSTANCE: the-man-No.017 man
SINGLETON: the-man-No.018 INSTANCE: the-man-No.018 man
SINGLETON: the-man-No.019 INSTANCE: the-man-No.019 man
SINGLETON: the-man-No.020 INSTANCE: the-man-No.020 man
SINGLETON: the-man-No.021 INSTANCE: the-man-No.021 man
SINGLETON: the-man-No.022 INSTANCE: the-man-No.022 man
SINGLETON: the-man-No.023 INSTANCE: the-man-No.023 man
SINGLETON: the-man-No.024 INSTANCE: the-man-No.024 man
SINGLETON: the-man-No.025 INSTANCE: the-man-No.025 man
SINGLETON: the-man-No.026 INSTANCE: the-man-No.026 man
SINGLETON: the-man-No.027 INSTANCE: the-man-No.027 man
SINGLETON: the-man-No.028 INSTANCE: the-man-No.028 man
SINGLETON: the-man-No.029 INSTANCE: the-man-No.029 man
SINGLETON: the-man-No.030 INSTANCE: the-man-No.030 man


GENERIC: sd-ln-beats? ( man1 man2 -- ? )

M: the-man-No.001 sd-ln-beats? 2drop t ;
M: the-man-No.002 sd-ln-beats? 2drop t ;
M: the-man-No.003 sd-ln-beats? 2drop t ;
M: the-man-No.004 sd-ln-beats? 2drop t ;
M: the-man-No.005 sd-ln-beats? 2drop t ;
M: the-man-No.006 sd-ln-beats? 2drop t ;
M: the-man-No.007 sd-ln-beats? 2drop t ;
M: the-man-No.008 sd-ln-beats? 2drop t ;
M: the-man-No.009 sd-ln-beats? 2drop t ;
M: the-man-No.010 sd-ln-beats? 2drop t ;
M: the-man-No.011 sd-ln-beats? 2drop t ;
M: the-man-No.012 sd-ln-beats? 2drop t ;
M: the-man-No.013 sd-ln-beats? 2drop t ;
M: the-man-No.014 sd-ln-beats? 2drop t ;
M: the-man-No.015 sd-ln-beats? 2drop t ;
M: the-man-No.016 sd-ln-beats? 2drop t ;
M: the-man-No.017 sd-ln-beats? 2drop t ;
M: the-man-No.018 sd-ln-beats? 2drop t ;
M: the-man-No.019 sd-ln-beats? 2drop t ;
M: the-man-No.020 sd-ln-beats? 2drop t ;
M: the-man-No.021 sd-ln-beats? 2drop t ;
M: the-man-No.022 sd-ln-beats? 2drop t ;
M: the-man-No.023 sd-ln-beats? 2drop t ;
M: the-man-No.024 sd-ln-beats? 2drop t ;
M: the-man-No.025 sd-ln-beats? 2drop t ;
M: the-man-No.026 sd-ln-beats? 2drop t ;
M: the-man-No.027 sd-ln-beats? 2drop t ;
M: the-man-No.028 sd-ln-beats? 2drop t ;
M: the-man-No.029 sd-ln-beats? 2drop t ;
M: the-man-No.030 sd-ln-beats? 2drop t ;


MGENERIC: md-ln-beats? ( man man -- ? )

MM: md-ln-beats? ( :man :the-man-No.001 -- ? ) 2drop t ;
MM: md-ln-beats? ( :man :the-man-No.002 -- ? ) 2drop t ;
MM: md-ln-beats? ( :man :the-man-No.003 -- ? ) 2drop t ;
MM: md-ln-beats? ( :man :the-man-No.004 -- ? ) 2drop t ;
MM: md-ln-beats? ( :man :the-man-No.005 -- ? ) 2drop t ;
MM: md-ln-beats? ( :man :the-man-No.006 -- ? ) 2drop t ;
MM: md-ln-beats? ( :man :the-man-No.007 -- ? ) 2drop t ;
MM: md-ln-beats? ( :man :the-man-No.008 -- ? ) 2drop t ;
MM: md-ln-beats? ( :man :the-man-No.009 -- ? ) 2drop t ;
MM: md-ln-beats? ( :man :the-man-No.010 -- ? ) 2drop t ;
MM: md-ln-beats? ( :man :the-man-No.011 -- ? ) 2drop t ;
MM: md-ln-beats? ( :man :the-man-No.012 -- ? ) 2drop t ;
MM: md-ln-beats? ( :man :the-man-No.013 -- ? ) 2drop t ;
MM: md-ln-beats? ( :man :the-man-No.014 -- ? ) 2drop t ;
MM: md-ln-beats? ( :man :the-man-No.015 -- ? ) 2drop t ;
MM: md-ln-beats? ( :man :the-man-No.016 -- ? ) 2drop t ;
MM: md-ln-beats? ( :man :the-man-No.017 -- ? ) 2drop t ;
MM: md-ln-beats? ( :man :the-man-No.018 -- ? ) 2drop t ;
MM: md-ln-beats? ( :man :the-man-No.019 -- ? ) 2drop t ;
MM: md-ln-beats? ( :man :the-man-No.020 -- ? ) 2drop t ;
MM: md-ln-beats? ( :man :the-man-No.021 -- ? ) 2drop t ;
MM: md-ln-beats? ( :man :the-man-No.022 -- ? ) 2drop t ;
MM: md-ln-beats? ( :man :the-man-No.023 -- ? ) 2drop t ;
MM: md-ln-beats? ( :man :the-man-No.024 -- ? ) 2drop t ;
MM: md-ln-beats? ( :man :the-man-No.025 -- ? ) 2drop t ;
MM: md-ln-beats? ( :man :the-man-No.026 -- ? ) 2drop t ;
MM: md-ln-beats? ( :man :the-man-No.027 -- ? ) 2drop t ;
MM: md-ln-beats? ( :man :the-man-No.028 -- ? ) 2drop t ;
MM: md-ln-beats? ( :man :the-man-No.029 -- ? ) 2drop t ;
MM: md-ln-beats? ( :man :the-man-No.030 -- ? ) 2drop t ;

  
MGENERIC: smd-ln-beats? ( man man -- ? )

MM: smd-ln-beats? ( man :the-man-No.001 -- ? ) 2drop t ;
MM: smd-ln-beats? ( man :the-man-No.002 -- ? ) 2drop t ;
MM: smd-ln-beats? ( man :the-man-No.003 -- ? ) 2drop t ;
MM: smd-ln-beats? ( man :the-man-No.004 -- ? ) 2drop t ;
MM: smd-ln-beats? ( man :the-man-No.005 -- ? ) 2drop t ;
MM: smd-ln-beats? ( man :the-man-No.006 -- ? ) 2drop t ;
MM: smd-ln-beats? ( man :the-man-No.007 -- ? ) 2drop t ;
MM: smd-ln-beats? ( man :the-man-No.008 -- ? ) 2drop t ;
MM: smd-ln-beats? ( man :the-man-No.009 -- ? ) 2drop t ;
MM: smd-ln-beats? ( man :the-man-No.010 -- ? ) 2drop t ;
MM: smd-ln-beats? ( man :the-man-No.011 -- ? ) 2drop t ;
MM: smd-ln-beats? ( man :the-man-No.012 -- ? ) 2drop t ;
MM: smd-ln-beats? ( man :the-man-No.013 -- ? ) 2drop t ;
MM: smd-ln-beats? ( man :the-man-No.014 -- ? ) 2drop t ;
MM: smd-ln-beats? ( man :the-man-No.015 -- ? ) 2drop t ;
MM: smd-ln-beats? ( man :the-man-No.016 -- ? ) 2drop t ;
MM: smd-ln-beats? ( man :the-man-No.017 -- ? ) 2drop t ;
MM: smd-ln-beats? ( man :the-man-No.018 -- ? ) 2drop t ;
MM: smd-ln-beats? ( man :the-man-No.019 -- ? ) 2drop t ;
MM: smd-ln-beats? ( man :the-man-No.020 -- ? ) 2drop t ;
MM: smd-ln-beats? ( man :the-man-No.021 -- ? ) 2drop t ;
MM: smd-ln-beats? ( man :the-man-No.022 -- ? ) 2drop t ;
MM: smd-ln-beats? ( man :the-man-No.023 -- ? ) 2drop t ;
MM: smd-ln-beats? ( man :the-man-No.024 -- ? ) 2drop t ;
MM: smd-ln-beats? ( man :the-man-No.025 -- ? ) 2drop t ;
MM: smd-ln-beats? ( man :the-man-No.026 -- ? ) 2drop t ;
MM: smd-ln-beats? ( man :the-man-No.027 -- ? ) 2drop t ;
MM: smd-ln-beats? ( man :the-man-No.028 -- ? ) 2drop t ;
MM: smd-ln-beats? ( man :the-man-No.029 -- ? ) 2drop t ;
MM: smd-ln-beats? ( man :the-man-No.030 -- ? ) 2drop t ;


CONSTANT: COMBI-TIMES 100,000

"\n"
COMBI-TIMES [
    { [ dup 1,000,000 >= ] [
          [ 1,000,000 / >integer ]
          [ 1,000,000 mod 1,000 / >integer ]
          [ 1,000 mod ] 
          tri "%d,%03d,%03d" sprintf ] }
    { [ dup 1,000 >= ] [
          [ 1,000 / >integer ]
          [ 1,000 mod ] 
          bi "%d,%03d" sprintf ] }
    [ "%d" sprintf ]
] cond
" repetitions of the showdown of the all combinations of No.001 to No.005\n" 3append printf

gc
[
    COMBI-TIMES [
        the-man-No.001 the-man-No.001 sd-ln-beats? drop
        the-man-No.001 the-man-No.002 sd-ln-beats? drop
        the-man-No.001 the-man-No.003 sd-ln-beats? drop
        the-man-No.001 the-man-No.004 sd-ln-beats? drop
        the-man-No.001 the-man-No.005 sd-ln-beats? drop
        the-man-No.002 the-man-No.001 sd-ln-beats? drop
        the-man-No.002 the-man-No.002 sd-ln-beats? drop
        the-man-No.002 the-man-No.003 sd-ln-beats? drop
        the-man-No.002 the-man-No.004 sd-ln-beats? drop
        the-man-No.002 the-man-No.005 sd-ln-beats? drop
        the-man-No.003 the-man-No.001 sd-ln-beats? drop
        the-man-No.003 the-man-No.002 sd-ln-beats? drop
        the-man-No.003 the-man-No.003 sd-ln-beats? drop
        the-man-No.003 the-man-No.004 sd-ln-beats? drop
        the-man-No.003 the-man-No.005 sd-ln-beats? drop
        the-man-No.004 the-man-No.001 sd-ln-beats? drop
        the-man-No.004 the-man-No.002 sd-ln-beats? drop
        the-man-No.004 the-man-No.003 sd-ln-beats? drop
        the-man-No.004 the-man-No.004 sd-ln-beats? drop
        the-man-No.004 the-man-No.005 sd-ln-beats? drop
        the-man-No.005 the-man-No.001 sd-ln-beats? drop
        the-man-No.005 the-man-No.002 sd-ln-beats? drop
        the-man-No.005 the-man-No.003 sd-ln-beats? drop
        the-man-No.005 the-man-No.004 sd-ln-beats? drop
        the-man-No.005 the-man-No.005 sd-ln-beats? drop
    ] times
] benchmark dup ref namespaces:set
1.0e9 /
"single-dispatch:            %.6f　seconds (reference)\n" printf

gc
[
    COMBI-TIMES [
        the-man-No.001 the-man-No.001 md-ln-beats? drop
        the-man-No.001 the-man-No.002 md-ln-beats? drop
        the-man-No.001 the-man-No.003 md-ln-beats? drop
        the-man-No.001 the-man-No.004 md-ln-beats? drop
        the-man-No.001 the-man-No.005 md-ln-beats? drop
        the-man-No.002 the-man-No.001 md-ln-beats? drop
        the-man-No.002 the-man-No.002 md-ln-beats? drop
        the-man-No.002 the-man-No.003 md-ln-beats? drop
        the-man-No.002 the-man-No.004 md-ln-beats? drop
        the-man-No.002 the-man-No.005 md-ln-beats? drop
        the-man-No.003 the-man-No.001 md-ln-beats? drop
        the-man-No.003 the-man-No.002 md-ln-beats? drop
        the-man-No.003 the-man-No.003 md-ln-beats? drop
        the-man-No.003 the-man-No.004 md-ln-beats? drop
        the-man-No.003 the-man-No.005 md-ln-beats? drop
        the-man-No.004 the-man-No.001 md-ln-beats? drop
        the-man-No.004 the-man-No.002 md-ln-beats? drop
        the-man-No.004 the-man-No.003 md-ln-beats? drop
        the-man-No.004 the-man-No.004 md-ln-beats? drop
        the-man-No.004 the-man-No.005 md-ln-beats? drop
        the-man-No.005 the-man-No.001 md-ln-beats? drop
        the-man-No.005 the-man-No.002 md-ln-beats? drop
        the-man-No.005 the-man-No.003 md-ln-beats? drop
        the-man-No.005 the-man-No.004 md-ln-beats? drop
        the-man-No.005 the-man-No.005 md-ln-beats? drop
    ] times
] benchmark
[ 1.0e9 / ] [ ref get / ] bi
"multi-dispatch:             %.6f　seconds (%.2f times slower)\n" printf

gc
[
    COMBI-TIMES [
        the-man-No.001 the-man-No.001 smd-ln-beats? drop
        the-man-No.001 the-man-No.002 smd-ln-beats? drop
        the-man-No.001 the-man-No.003 smd-ln-beats? drop
        the-man-No.001 the-man-No.004 smd-ln-beats? drop
        the-man-No.001 the-man-No.005 smd-ln-beats? drop
        the-man-No.002 the-man-No.001 smd-ln-beats? drop
        the-man-No.002 the-man-No.002 smd-ln-beats? drop
        the-man-No.002 the-man-No.003 smd-ln-beats? drop
        the-man-No.002 the-man-No.004 smd-ln-beats? drop
        the-man-No.002 the-man-No.005 smd-ln-beats? drop
        the-man-No.003 the-man-No.001 smd-ln-beats? drop
        the-man-No.003 the-man-No.002 smd-ln-beats? drop
        the-man-No.003 the-man-No.003 smd-ln-beats? drop
        the-man-No.003 the-man-No.004 smd-ln-beats? drop
        the-man-No.003 the-man-No.005 smd-ln-beats? drop
        the-man-No.004 the-man-No.001 smd-ln-beats? drop
        the-man-No.004 the-man-No.002 smd-ln-beats? drop
        the-man-No.004 the-man-No.003 smd-ln-beats? drop
        the-man-No.004 the-man-No.004 smd-ln-beats? drop
        the-man-No.004 the-man-No.005 smd-ln-beats? drop
        the-man-No.005 the-man-No.001 smd-ln-beats? drop
        the-man-No.005 the-man-No.002 smd-ln-beats? drop
        the-man-No.005 the-man-No.003 smd-ln-beats? drop
        the-man-No.005 the-man-No.004 smd-ln-beats? drop
        the-man-No.005 the-man-No.005 smd-ln-beats? drop
    ] times
] benchmark
[ 1.0e9 / ] [ ref get / ] bi
"single spec multi-dispatch: %.6f　seconds (%.2f times slower)\n" printf

MGENERIC: my-plus ( a b -- c ) mathematical

USING: math.private ;
MM: my-plus ( a: fixnum b: fixnum -- c ) fixnum+ ;
MM: my-plus ( a: bignum b: bignum -- c ) bignum+ ;
MM: my-plus ( a: float b: float -- c ) float+ ;

USE: math.complex.private
MM: my-plus ( a: complex b: complex -- c ) [ my-plus ] complex-op ;

USE: math.ratios.private
MM: my-plus ( a: ratio b: ratio -- c ) scale+d [ my-plus ] [ / ] bi* ;

{ 3 3.0 3.0 1+1/6 1.0 C{ 2.0 -1 } } [
    1 2 my-plus
    1.0 2 my-plus
    1 2.0 my-plus
    1/2 2/3 my-plus
    0.5 1/2 my-plus
    C{ 0 -1 } 2.0 my-plus
] unit-test


MGENERIC: md-beats2? ( obj1 obj2 -- ? )

MM:: md-beats2? ( obj1: paper obj2: scissors -- ? ) obj1 "scissors beats %s!\n" printf t ;
MM:: md-beats2? ( obj1: scissors obj2: rock -- ? ) obj2 "%s beats scissors!\n" printf t ;
MM:: md-beats2? ( o1: rock o2: paper -- ? ) o2 o1 "%s beats %s!\n" printf t ;
MM:: md-beats2? ( thing1: thing thing2: thing -- ? ) thing2 thing1 "%s doesn't beat %s.\n" printf f ;

: md-play2 ( obj1 obj2 -- ? ) md-beats2? ;

{ f t f  f f t  t f f } [ 
    paper paper       md-play2
    paper scissors    md-play2
    paper rock        md-play2
    
    scissors paper    md-play2
    scissors scissors md-play2
    scissors rock     md-play2
    
    rock paper        md-play2
    rock scissors     md-play2
    rock rock         md-play2
] unit-test


MGENERIC: smd-beats2? ( obj1 obj2 -- ? )

MM:: smd-beats2? ( obj1 obj2: paper -- ? )    obj1 rock? [ t ] [ f ] if obj1 "%s vs. paper\n" printf ; 
MM:: smd-beats2? ( obj1 obj2: scissors -- ? ) obj1 paper? [ t ] [ f ] if obj1 obj2 "%s vs. %s\n" printf ;
MM:: smd-beats2? ( o1 o2: rock -- ? )         o1 scissors? [ t ] [ f ] if o1 "%s vs. rock\n" printf ;

: smd-play2 ( obj1 obj2 -- ? ) smd-beats2? ;

{ f t f  f f t  t f f } [
    paper paper       smd-play2
    paper scissors    smd-play2
    paper rock        smd-play2
    
    scissors paper    smd-play2
    scissors scissors smd-play2
    scissors rock     smd-play2
    
    rock paper        smd-play2
    rock scissors     smd-play2
    rock rock         smd-play2
] unit-test


TUPLE: test-tuple1 ;
TUPLE: test-tuple2 < test-tuple1 ;
TUPLE: test-tuple3 < test-tuple2 ;

MGENERIC: next-method-test ( class -- who-i-am )

MM: next-method-test ( class: test-tuple1 -- who-i-am )
    drop "test-tuple1" ;

MM: next-method-test ( class: test-tuple2 -- who-i-am )
    "subclass of " swap call-next-multi-method append ;

MM: next-method-test ( class: test-tuple3 -- who-i-am )
    drop "test-tuple3" ;

test-tuple1 new next-method-test .
test-tuple2 new next-method-test .
test-tuple3 new next-method-test .



