
USING: combinators formatting kernel math mm prettyprint
sequences tools.time ;

IN: mm.tests


MIXIN: thing

SINGLETON: paper    INSTANCE: paper thing
SINGLETON: scissors INSTANCE: scissors thing
SINGLETON: rock     INSTANCE: rock thing

! multi-dispatch
MGENERIC: md-beats? ( obj1 obj2 -- ? )

MM: md-beats? ( obj1: paper obj2: scissors -- ? ) 2drop t ;
MM: md-beats? ( obj1: scissors obj2: rock -- ? ) 2drop t ;
MM: md-beats? ( obj1: rock obj2: paper -- ? ) 2drop t ;
MM: md-beats? ( obj1: thing obj2: thing -- ? ) 2drop f ;

: md-play ( obj1 obj2 -- ? ) md-beats? ;


! sigle-dispach
GENERIC: sd-beats? ( obj1 obj2 -- ? )

M: paper sd-beats? drop rock? [ t ] [ f ] if ; 
M: scissors sd-beats? drop paper? [ t ] [ f ] if ;
M: rock sd-beats? drop scissors? [ t ] [ f ] if ;
M: thing sd-beats? 2drop f ;

: sd-play ( obj1 obj2 -- ? ) sd-beats? ;


! no-dispatch
: beats? ( obj1 obj2 -- ? )
    {
        { rock     [ scissors? [ t ] [ f ] if ] }
        { paper    [ rock?     [ t ] [ f ] if ] }
        { scissors [ paper?    [ t ] [ f ] if ] }
    } case ;

: play ( obj1 obj2 -- ? ) beats? ;


CONSTANT: TIMES 100,000

"Repeat all combinations of rock-paper-scissors "
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
] benchmark 1.0e9 / "multi-dispatch:  %.6f seconds\n" printf

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
] benchmark 1.0e9 / "single-dispatch: %.6f seconds\n" printf


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
] benchmark 1.0e9 / "no-dispatch:     %.6f seconds\n" printf





