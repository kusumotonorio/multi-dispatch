USING: arrays combinators formatting kernel math math.ranges
memory mm6 namespaces prettyprint quotations sequences
tools.test tools.time ;
IN: mm6.tests

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

! multi-sigle-dispach
MGENERIC: msd-beats? ( obj1 obj2 -- ? )

MM: msd-beats? ( obj1 obj2: paper -- ? )    drop rock? [ t ] [ f ] if ; 
MM: msd-beats? ( obj1 obj2: scissors -- ? ) drop paper? [ t ] [ f ] if ;
MM: msd-beats? ( obj1 obj2: rock -- ? )     drop scissors? [ t ] [ f ] if ;

: msd-play ( obj1 obj2 -- ? ) msd-beats? ;

{ 
    f t f  f f t  t f f 
    f t f  f f t  t f f 
} [
    2 [
        paper paper       msd-play
        paper scissors    msd-play
        paper rock        msd-play
        
        scissors paper    msd-play
        scissors scissors msd-play
        scissors rock     msd-play
        
        rock paper        msd-play
        rock scissors     msd-play
        rock rock         msd-play
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

MM: hook-beats-stack?-2 ( thing1: paper thing2: paper |
                          a: rock b: rock -- ? ) 2drop t ;

MM: hook-beats-stack?-2 ( thing1: scissors thing2: scissors |
                          a: paper b: paper -- ? ) 2drop t ;

MM: hook-beats-stack?-2 ( thing1: rock thing2: rock |
                          a: scissors b: scissors -- ? ) 2drop t ;

MM: hook-beats-stack?-2 ( thing1: thing thing2: thing |
                          a: thing b: thing -- ? ) 2drop f ;

{ t f } [
    paper thing1 set paper thing2 set    rock rock hook-beats-stack?
    scissors thing1 set paper thing2 set rock rock hook-beats-stack?    
] unit-test


! MGENERIC: dispatch#1 ( a *b* c -- d )

! MM: dispatch#1 ( a: object b: integer c: object -- d ) 3drop "integer" ;
! MM: dispatch#1 ( a b: object c -- d ) 3drop "Something other than integer" ;

! { "integer" "Something other than integer" "integer" } [
!     1 2 3 dispatch#1
!     1 2.0 3 dispatch#1
!     1.0 2 3.0 dispatch#1
! ] unit-test


CONSTANT: TIMES 100,000
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
1.0e9 / "no-dispatch:              %.6f seconds (reference)\n" printf

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
"single-dispatch:          %.6f seconds (%.2f times slower)\n" printf

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
"multi-dispatch:           %.6f seconds (%.2f times slower)\n" printf

! gc
! [
!     TIMES [
!         paper paper       msd-play drop
!         paper paper       msd-play drop
!         paper paper       msd-play drop
!         paper paper       msd-play drop
!         paper paper       msd-play drop
!         paper paper       msd-play drop
!         paper paper       msd-play drop
!         paper paper       msd-play drop
!         paper paper       msd-play drop        
!     ] times
! ] benchmark
! [ 1.0e9 / ] [ no-dispatch-time get / ] bi
! "single-dispatch on multi: %.6f seconds (%.2f times slower)\n" printf

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
"single-hook-dispatch:     %.6f seconds (%.2f times slower)\n" printf

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
"multi-hook-dispatch:      %.6f seconds (%.2f times slower)\n" printf
