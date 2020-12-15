! Borrowing the `multi-methods`

USING: accessors arrays assocs classes classes.algebra
combinators compiler.units debugger definitions effects
effects.parser generalizations generic.parser hashtables io
kernel kernel.private locals.parser make math math.order
namespaces parser prettyprint prettyprint.backend
prettyprint.custom prettyprint.sections quotations see sequences
sequences.generalizations sets shuffle sorting splitting vectors
words ;
FROM: namespaces => set ;
IN: mm5

TUPLE: multi-method-combination
    hooks 
    cache-key dispatched-method 
    method-cache ;

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
       [ "combination-type" word-prop hooks>> ]
         bi :> ( in out hooks )
        hooks [ in ] [ { "|" } in 3append ] if-empty out <effect> ;

:: effect>specializer ( effect -- specializer )
    effect parse-variable-effect :> ( eff vars )
    eff in>> [
        dup array? [
            second dup effect? [ drop callable ] when
        ] [
            drop object
        ] if
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
    ] 2curry find [ "Topological sort failed" throw ] unless* ; inline

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

: class/item ( item -- class/item )
    dup class? [
        dup predicate? [ class-of ] unless
    ] unless ; inline

:: attach-cache ( quot -- quot' )
    quot last :> method 
    method "multi-method-generic" word-prop :> generic
    generic "declared-effect" word-prop in>> length :> stack-length
    generic "combination-type" word-prop method-cache>> :> method-cache
    generic "combination-type" word-prop :> multi-combination
    quot '[
        multi-combination quot method-cache
        quot multi-combination
        '[
            _ cache-key>> _ swap _ set-at 
            _ _ dispatched-method<<
        ] %
        _ %
    ] [ ] make ;

:: attach-cache-exec ( quot generic -- quot' )
    generic "declared-effect" word-prop :> effect
    effect in>> length :> stack-length
    generic "combination-type" word-prop hooks>> length :> hooks-length
    hooks-length stack-length + :> total-length
    effect [
        in>> hooks-length "x" <array> append
    ] [ out>> ] bi <effect> :> drop-n-effect 
    stack-length '[ _ ndup ]
    generic "combination-type" word-prop hooks>> [ '[ _ get ] ] map concat append
    total-length '[ _ narray ] append :> key-array
    [ drop ] quot append :> cache-miss-quot
    generic "combination-type" word-prop :> multi-combination
    multi-combination method-cache>> :> method-cache
    key-array '[
        _ %
        multi-combination
        multi-combination drop-n-effect
        multi-combination method-cache drop-n-effect cache-miss-quot
        '[
            [ class/item ] map dup _ cache-key>> = [
                drop _ dispatched-method>> _ call-effect
            ] [
                dup _ cache-key<< _ at dup [ _ call-effect ] _ if 
            ] if
        ] %
    ] [ ] make ;

CONSTANT: CACHE-THRESHOLD 100

:: multi-dispatch-quot ( methods generic -- quot )
    methods length CACHE-THRESHOLD >= :> cache?  
    methods generic make-default-method
    methods cache? [ [ attach-cache ] assoc-map ] when
    [ [ multi-predicate ] dip ] assoc-map reverse!
    alist>quot
    cache? [ generic attach-cache-exec ] when ;

! Generic words
PREDICATE: mm-generic < word
    "multi-methods" word-prop >boolean ;

: methods ( word -- alist )
    "multi-methods" word-prop >alist ;

: make-generic ( generic -- quot )
    [
        [ methods prepare-methods % sort-methods ] keep
        multi-dispatch-quot %
    ] [ ] make ;

: update-generic ( word -- )
    dup "combination-type" word-prop H{ } clone swap method-cache<<
    dup make-generic 
    define ;

! Methods
PREDICATE: method-body < word
    "multi-method-generic" word-prop >boolean ;

M: method-body stack-effect
    "multi-method-generic" word-prop stack-effect ;

M: method-body crossref?
    "forgotten" word-prop not ;

: method-word-name ( specializer generic -- string )
    [ name>> % " " % unparse % ] "" make ;

: method-word-props ( effect specializer generic -- assoc )
    [
        "multi-method-generic" ,,
        "multi-method-specializer" ,,
        "declared-effect" ,,
    ] H{ } make ;

: <method> ( effect specializer generic -- word )
    [ method-word-props ] 3keep nip ! 2keep
    [  ] dip
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

:: create-method ( effect classes generic -- method )
    effect classes generic
    2dup method dup [
        2nip
    ] [
        drop [ effect -rot <method> dup ] 2keep reveal-method
    ] if
    dup rot drop effect set-stack-effect ;

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
    [ over  multi-method-combination new "combination-type" set-word-prop ] dip
    [ over swap set-stack-effect ] dip
    over "combination-type" word-prop hooks<<
    dup "multi-methods" word-prop [ drop ] [              ! ???
        [ H{ } clone "multi-methods" set-word-prop ]
        [ "combination-type" word-prop H{ } clone swap method-cache<< ]
        [ update-generic ]
        tri
    ] if ;

! Syntax
SYNTAX: MGENERIC: scan-new-word scan-effect 
    parse-variable-effect
    define-generic ;

: create-method-in ( effect specializer generic -- method )
    create-method dup save-location f set-last-word ;

: scan-new-method ( -- method )
    scan-word scan-effect
    dup effect>specializer rot create-method-in ;

: (MM:) ( -- method def ) scan-new-method parse-definition ;

SYNTAX: MM: (MM:) define ;


! Definition protocol. We qualify core generics here

M: mm-generic definer drop \ MGENERIC: f ;

M: mm-generic definition drop f ;

PREDICATE: method-spec < array
    unclip mm-generic? [ [ class? ] all? ] dip and ;

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
    [ "declared-effect" word-prop pprint* ]
    bi ;

SYNTAX: MM\
    scan-word scan-effect effect>specializer
    swap method <wrapper> suffix! ;

M: method-body pprint*
    <block
    \ MM\ pprint-word
    [ "multi-method-generic" word-prop pprint-word ]
    [ "declared-effect" word-prop pprint* ]
    bi
    block> ;
