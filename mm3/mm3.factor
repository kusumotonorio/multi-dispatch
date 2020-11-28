! Borrowing the `multi-methods`

USING: accessors arrays assocs classes classes.algebra
combinators compiler.units debugger definitions effects
effects.parser generalizations hashtables io kernel
kernel.private make math math.order namespaces parser
prettyprint prettyprint.backend prettyprint.custom quotations
see sequences sequences.generalizations sets shuffle sorting
splitting vectors words ;
FROM: namespaces => set ;
IN: mm3

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

: correlate ( seq assoc -- seq' )
    '[ _ at object or ] map ;

:: effect>specializer ( generic effect -- specializer )
    effect parse-variable-effect :> ( eff vars )
    eff in>> [
        dup array? [
            second dup effect? [ drop callable ] when
        ] [ parse-word ] if
    ] map
    vars append ;

! PART I: Converting hook specializers
: canonicalize-specializer-0 ( specializer -- specializer' )
    [ \ f or ] map ;

SYMBOL: args

SYMBOL: hooks

SYMBOL: total

: canonicalize-specializer-1 ( specializer -- specializer' )
    [
        [ class? ] filter
        [ length <iota> <reversed> [ 1 + neg ] map ] keep zip
        [ length args [ max ] change ] keep
    ]
    [
        [ pair? ] filter
        [ keys [ hooks get adjoin ] each ] keep
    ] bi append ;

: canonicalize-specializer-2 ( specializer -- specializer' )
    [
        [
            {
                { [ dup integer? ] [ ] }
                { [ dup word? ] [ hooks get index ] }
            } cond args get +
        ] dip
    ] assoc-map ;

: canonicalize-specializer-3 ( specializer -- specializer' )
    [ total get object <array> <enumerated> ] dip assoc-union! seq>> ;

: canonicalize-specializers ( methods -- methods' hooks )
    [
        [ [ canonicalize-specializer-0 ] dip ] assoc-map

        0 args set
        V{ } clone hooks set

        [ [ canonicalize-specializer-1 ] dip ] assoc-map

        hooks [ natural-sort ] change

        [ [ canonicalize-specializer-2 ] dip ] assoc-map

        args get hooks get length + total set

        [ [ canonicalize-specializer-3 ] dip ] assoc-map

        hooks get
    ] with-scope ;

: drop-n-quot ( n -- quot ) \ drop <repetition> >quotation ;

: prepare-method ( method n -- quot )
    [ 1quotation ] [ drop-n-quot ] bi* prepend ;

: prepare-methods ( methods -- methods' prologue )
    canonicalize-specializers
    [ length [ prepare-method ] curry assoc-map ] keep
    [ [ get ] curry ] map concat [ ] like ;

! Part II: Topologically sorting specializers
: maximal-element ( seq quot -- n elt )
    dupd [
        swapd [ call +lt+ = ] 2curry none?
    ] 2curry find [ "Topological sort failed" throw ] unless* ;
    inline

: topological-sort ( seq quot -- newseq )
    [ >vector [ dup empty? not ] ] dip
    [ dupd maximal-element [ over remove-nth! drop ] dip ] curry
    produce nip ; inline

: classes< ( seq1 seq2 -- lt/eq/gt )
    [
        {
            { [ 2dup eq? ] [ +eq+ ] }
            { [ 2dup [ class<= ] [ swap class<= ] 2bi and ] [ +eq+ ] }
            { [ 2dup class<= ] [ +lt+ ] }
            { [ 2dup swap class<= ] [ +gt+ ] }
            [ +eq+ ]
        } cond 2nip
    ] 2map [ +eq+ eq? not ] find nip +eq+ or ;

: sort-methods ( alist -- alist' )
    [ [ first ] bi@ classes< ] topological-sort ;

! PART III: Creating dispatch quotation
: picker ( n -- quot )
    {
        { 0 [ [ dup ] ] }
        { 1 [ [ over ] ] }
        { 2 [ [ pick ] ] }
        [ 1 - picker [ dip swap ] curry ]
    } case ;

: (multi-predicate) ( class picker -- quot )
    swap predicate-def append ;

: multi-predicate ( classes -- quot )
    dup length <iota> <reversed>
    [ picker 2array ] 2map
    [ drop object eq? ] assoc-reject
    [ [ t ] ] [
        [ (multi-predicate) ] { } assoc>map
        unclip [ swap [ f ] \ if 3array append [ ] like ] reduce
    ] if-empty ;

: argument-count ( methods -- n )
    keys 0 [ length max ] reduce ;

ERROR: no-method arguments generic ;

: make-default-method ( methods generic -- quot )
    [ argument-count ] dip [ [ narray ] dip no-method ] 2curry ;

: multi-dispatch-quot ( methods generic -- quot )
    [ make-default-method ]
    [ drop [ [ multi-predicate ] dip ] assoc-map reverse! ]
    2bi alist>quot ;

! Generic words
PREDICATE: generic < word
    "multi-methods" word-prop >boolean ;

: methods ( word -- alist )
    "multi-methods" word-prop >alist ;

: make-generic ( generic -- quot )
    [
        [ methods 
          prepare-methods 
          % sort-methods ] keep
        multi-dispatch-quot %
    ] [ ] make ;

: update-generic ( word -- )
    dup make-generic define ;

! Methods
PREDICATE: method-body < word
    "multi-method-generic" word-prop >boolean ;

M: method-body stack-effect
    "multi-method-generic" word-prop stack-effect ;

M: method-body crossref?
    "forgotten" word-prop not ;

: method-word-name ( specializer generic -- string )
    [ name>> % "-" % unparse % ] "" make ;

: method-word-props ( specializer generic -- assoc )
    [
        "multi-method-generic" ,,
        "multi-method-specializer" ,,
    ] H{ } make ;

: <method> ( specializer generic -- word )
    [ method-word-props ] 2keep
    method-word-name f <word>
    swap >>props ;

: with-methods ( word quot -- )
    over [
        [ "multi-methods" word-prop ] dip call
    ] dip update-generic ; inline

: reveal-method ( method classes generic -- )
    [ set-at ] with-methods ;

: method ( classes word -- method )
    "multi-methods" word-prop at ;

: create-method ( classes generic -- method )
    2dup method dup [
        2nip
    ] [
        drop [ <method> dup ] 2keep reveal-method
    ] if ;

: niceify-method ( seq -- seq )
    [ dup \ f eq? [ drop f ] when ] map ;

M: no-method error.
    "Type check error" print
    nl
    "Generic word " write dup generic>> pprint
    " does not have a method applicable to inputs:" print
    dup arguments>> short.
    nl
    "Inputs have signature:" print
    dup arguments>> [ class-of ] map niceify-method .
    nl
    "Available methods: " print
    generic>> methods canonicalize-specializers drop sort-methods
    keys [ niceify-method ] map stack. ;

: forget-method ( specializer generic -- )
    [ delete-at ] with-methods ;

: method>spec ( method -- spec )
    [ "multi-method-specializer" word-prop ]
    [ "multi-method-generic" word-prop ] bi prefix ;

: define-generic ( word effect hooks -- )
    [ over swap set-stack-effect ] dip
    dupd "hooks" set-word-prop
    dup "multi-methods" word-prop [ drop ] [
        [ H{ } clone "multi-methods" set-word-prop ]
        [ update-generic ]
        bi
    ] if ;

! Syntax
SYNTAX: MGENERIC: scan-new-word scan-effect 
    parse-variable-effect
    define-generic ;

: create-method-in ( specializer generic -- method )
    create-method dup save-location f set-last-word ;

: scan-new-method ( -- method )
    scan-word dup scan-effect effect>specializer swap create-method-in ;

: (MM:) ( -- method def ) scan-new-method parse-definition ;

SYNTAX: MM: (MM:) define ;


! Definition protocol. We qualify core generics here

M: generic definer drop \ GENERIC: f ;

M: generic definition drop f ;

PREDICATE: method-spec < array
    unclip generic? [ [ class? ] all? ] dip and ;

M: method-spec where
    dup unclip method [ ] [ first ] ?if where ;

M: method-spec set-where
    unclip method set-where ;

M: method-spec definer
    unclip method definer ;

M: method-spec definition
    unclip method definition ;

M: method-spec synopsis*
    unclip method synopsis* ;

M: method-spec forget*
    unclip method forget* ;

M: method-body definer
    drop \ MM: \ ; ;

M: method-body synopsis*
    dup definer.
    [ "multi-method-generic" word-prop pprint-word ]
    [ "multi-method-specializer" word-prop pprint* ] bi ;
