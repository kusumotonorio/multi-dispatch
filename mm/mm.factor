! Copyright (C) 2020 Your name.
! See http://factorcode.org/license.txt for BSD license.

USING: accessors arrays assocs classes.algebra combinators
combinators.short-circuit definitions effects effects.parser fry
generalizations kernel lexer locals make make.private math
math.order namespaces parser prettyprint quotations sequences
sequences.generalizations sets splitting words ;
FROM: namespaces => set ;
IN: mm

SINGLETON: D

! Dropping hook variables before method calls
: prepare-method ( method n -- quot )
    swap '[ _ ndrop _ execute ] ;

: prepare-methods ( methods generic -- methods' prologue )
    "hooks" word-prop
    [ length [ prepare-method ] curry assoc-map ] keep
    [ [ get ] curry ] map concat [ ] like ;

! Topologically sorting specializers, online as they are added
: classes< ( seq1 seq2 -- lt/eq/gt )
    [
        {
            { [ 2dup eq? ] [ +eq+ ] }
            { [ 2dup [ class<= ] [ swap class<= ] 2bi and ] [ +eq+ ] }
            { [ 2dup class<= ] [ +lt+ ] }
            { [ 2dup swap class<= ] [ +gt+ ] }
            [ +eq+ ]
        } cond 2nip
    ] 2map [ +eq+ = not ] find nip +eq+ or ;

: insert-nth! ( elt i seq -- )
    {
        [ swap tail ]
        [ set-length ]
        [ nip swapd push ]
        [ nip push-all ]
    } 2cleave ;

: find-position ( spec/method method-list -- i )
    [ [ first ] bi@ class< +gt+ = ] with find-last drop
    0 or ;

: insert-method ( spec/method method-list -- )
    2dup find-position swap insert-nth! ;

ERROR: no-method arguments generic ;

: make-default-method ( generic -- quot )
    [ stack-effect in>> length ] keep
    [ "hooks" word-prop ] keep
    [ [ narray ] [ [ get ] map append ] [ ] tri* no-method ] 3curry ;

PREDICATE: mm-generic < word
    "multi-methods" word-prop >boolean ;

: methods ( word -- alist )
    "method-list" word-prop ;

: [works?] ( len -- quot )
    <iota> [
        [ 1 + ] keep '[
            [ _ npick ] dip
            _ swap nth
            call( object -- ? )
        ]
    ] map '[ _ 1&& ] ;

: prepare-specifier ( specifier -- specifier' )
    reverse [ "predicate" word-prop ] map ;

MACRO:: dispatch ( hooks effect default -- quot )
    effect in>> length :> #args
    #args hooks length + [works?] :> checker
    [
        hooks [ '[ _ get ] ] map concat '[ _ dip ] %
        [ [ third checker call ] find-last nip ] %
        hooks length '[ _ nnip ] %
        [
            [ second effect execute-effect ]
            [ default effect call-effect ] if*
        ] %
    ] [ ] make ;

: make-generic ( generic -- quot )
    {
        [ methods ]
        [ "hooks" word-prop ]
        [ stack-effect ]
        [ make-default-method ]
    } cleave
    '[ _ _ _ _ dispatch ] ;

: update-generic ( word -- )
    dup make-generic define ;

PREDICATE: mm-body < word
    "mm-generic" word-prop >boolean ;

M: mm-body stack-effect
    "mm-generic" word-prop stack-effect ;

M: mm-body crossref?
    "forgotten" word-prop not ;

: method-word-name ( specializer generic -- string )
    [ name>> % "-" % unparse % ] "" make ;

: method-word-props ( specializer generic -- assoc )
    [
        "mm-generic" set
        "mm-specializer" set
    ] H{ } make-assoc ;

ERROR: extra-hooks ;

: check-hooks ( specializer generic -- )
    [ [ array? ] filter [ first ] map ]
    [ "hooks" word-prop ]
    bi*
    subset? [ extra-hooks ] unless ;

: <method> ( specializer generic -- word )
    2dup check-hooks
    [ method-word-props ] 2keep
    method-word-name f <word>
    swap >>props ;

: with-methods ( word quot -- )
    over [
        [ "multi-methods" word-prop ] dip call
    ] dip update-generic ; inline

: reveal-method ( method classes generic -- )
    [
        [ swap over prepare-specifier 3array ]
        [ "method-list" word-prop ] bi* insert-method ]
    [ [ set-at ] with-methods ]
    3bi ;

: method ( classes word -- method )
    "multi-methods" word-prop at ;

: create-method ( classes generic -- method )
    2dup method dup [ 2nip ] [ 
        drop [ <method> dup ] 2keep reveal-method
    ] if ;

: niceify-method ( seq -- seq )
    [ dup \ f eq? [ drop f ] when ] map ;

: forget-method ( specializer generic -- )
    [ "method-list" word-prop swap '[ first _ = not ] filter! drop ]
    [ [ delete-at ] with-methods ]
    2bi ;

M: mm-body forget*
    [
        "multi-method-specializer" "multi-method-generic"
        [ word-prop ] bi-curry@ bi forget-method ] 
    [ call-next-method ]
    bi ;

M: mm-generic forget*
    [ methods values [ forget ] each ] [ call-next-method ] bi ;


: define-generic ( word effect hooks -- )
    [ over swap set-stack-effect ] dip
    ! If hooks is already set to something, then
    ! method-list and multi-methods need to be modified
    dupd "hooks" set-word-prop
    dup "multi-methods" word-prop [ drop ] [
        [ V{ } clone "method-list" set-word-prop ]
        [ H{ } clone "multi-methods" set-word-prop ]
        [ update-generic ]
        tri
    ] if ;

! for my syntax
: parse-variable-effect ( effect -- effect' hooks )
    [ 
        in>> { "|" } split1 [ 
            [
                [
                    dup array? [ 
                        first2 [ parse-word ] dip 2array
                    ] [ parse-word ] if
                ] map
            ] dip
        ] [ 
            { } clone swap 
        ] if* ] 
    [ out>> ]
    bi <effect> swap ;

:: generic-stack-effect ( generic -- effect )
        generic
        [ stack-effect [ in>> ] [ out>> ] bi ]
        [ "hooks" word-prop ]
        bi :> ( in out hooks )
        hooks [ in ] [ { "|" } in 3append ] if-empty out <effect> ;

! : parse-variable-effect ( effect -- effect' variables )
!     [ in>> ] 
!     [ out>> { "|" } split1 ] bi
!     [ <effect> ] [
!         [
!             dup array?
!             [ first2 [ parse-word ] dip 2array ]
!             [ parse-word ] if
!         ] map
!     ] bi* ;

! : generic-stack-effect ( generic -- effect )
!     [ stack-effect [ in>> ] [ out>> ] bi ]
!     [ "multi-hooks" word-prop ]
!     bi
!     [ { "|" } swap 3append ] unless-empty <effect> ;

: create-method-in ( specializer generic -- method )
    create-method dup save-location f set-last-word ;

: correlate ( seq assoc -- seq' )
    '[ _ at object or ] map ;

:: effect>specializer ( generic effect -- specializer )
    effect parse-variable-effect :> ( eff vars )
    eff in>> [
        dup array? [
            second dup effect?
            [ drop callable ] when
        ] [ parse-word ] if
    ] map
    generic "hooks" word-prop vars correlate
    append ;

: CREATE-METHOD ( -- method )
    scan-word scan-effect
    [ dupd effect>specializer swap create-method-in ] keep
    dupd "declared-effect" set-word-prop ;

: (MM:) ( -- method def ) CREATE-METHOD parse-definition ;

SYNTAX: MGENERIC:
    scan-token create-word-in
    scan-effect parse-variable-effect
    define-generic ;

SYNTAX: MM: (MM:) define ;





