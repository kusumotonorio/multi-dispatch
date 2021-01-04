! Borrowing the `multi-methods`

USING: accessors arrays assocs classes classes.algebra
classes.algebra.private classes.maybe classes.private
combinators combinators.private compiler compiler.units debugger
definitions effects effects.parser generalizations
generic.parser hashtables io kernel kernel.private layouts
locals.parser make math math.order math.private multiline
namespaces parser prettyprint prettyprint.backend
prettyprint.custom prettyprint.sections quotations see sequences
sequences.generalizations sets shuffle sorting splitting summary
vectors words words.symbol ;
FROM: namespaces => set ;
FROM: generic.single.private => inline-cache-miss
inline-cache-miss-tail lookup-method mega-cache-lookup
mega-cache-miss ;
IN: mm6

! USING: math.private ;

! PRIMITIVE: mega-cache-lookup ( methods index cache -- )
! PRIMITIVE: mega-cache-miss ( methods index cache -- method )

: sequence-hashcode-step' ( oldhash newpart -- newhash )
  integer>fixnum swap
  dup 9 fixnum-shift-fast fixnum+fast
  fixnum+fast ; inline

: sequence-hashcode' ( n seq -- x )
    [ 0 ] 2dip [ hashcode* sequence-hashcode-step' ] with each ;
    inline

: hashcode-test ( array -- hashcode )
    3 swap [ sequence-hashcode' ] recursive-hashcode ;


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

! Generic words
PREDICATE: mm-generic < word
    "multi-methods" word-prop >boolean ;

PREDICATE: single-generic < word
    "single-combination" word-prop >boolean ;

PREDICATE: method-body < word
    "multi-method-generic" word-prop >boolean ;

! SYMBOL: combination

TUPLE: multi-single-combination ;

TUPLE: multi-single-standard-combination < multi-single-combination # ;

TUPLE: multi-single-hook-combination < multi-single-combination var ;

SINGLETON: multi-math-combination

: make-mathematical ( word -- )
    t "mathematical" set-word-prop ;

SYNTAX: mathematical last-word make-mathematical ;


ERROR: bad-dispatch-position # ;

: <multi-single-standard-combination> ( # -- multi-single-standard-combination )
    dup integer? [ dup 0 < ] [ t ] if
    [ bad-dispatch-position ] when
    multi-single-standard-combination boa ;

C: <multi-single-hook-combination> multi-single-hook-combination

TUPLE: multi-method-combination
    hooks 
    cache-key dispatched-method 
    method-cache ;

GENERIC: make-single-default-method ( generic combination -- method )

GENERIC: perform-combination ( word combination -- )

GENERIC#: check-combination-effect 1 ( combination effect -- )

GENERIC: effective-method ( generic -- method )
\ effective-method t "no-compile" set-word-prop

: methods ( word -- alist )
    "multi-methods" word-prop >alist ;

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

! : with-combination ( combination quot -- )
!    [ combination ] dip with-variable ; inline


: picker ( n -- quot )
    {
        { 0 [ [ dup ] ] }
        { 1 [ [ over ] ] }
        { 2 [ [ pick ] ] }
        [ 1 - picker [ dip swap ] curry ]
    } case ;




! ---------------------------------------------------------------


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

:: specializers ( methods -- stack-specs hook-specs )
    V{ } clone :> stack-specializers
    V{ } clone :> hook-specializers
    methods keys [
        dup length <iota> reverse swap [
            dup array? [
                ! hook-specializer
                nip first dup hook-specializers in? [ drop ] [
                    hook-specializers push
                ] if
            ] [
                ! stack-specializer
                dup object = [ 2drop ] [ 
                    drop
                    dup stack-specializers in? [ drop ] [
                        stack-specializers push
                    ] if
                ] if
            ] if
        ] 2each
    ] each
    stack-specializers >array
    hook-specializers >array ;

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

:: multi-dispatch-quot ( methods generic -- quot )
        methods generic make-default-method
        methods [ [ multi-predicate ] dip ] assoc-map reverse!
        alist>quot ;

: make-single-generic ( word -- )
    [ "unannotated-def" remove-word-prop ]
    [ dup "single-combination" word-prop perform-combination ]
    bi ;

ERROR: check-method-error class generic ;

: check-single-method ( classoid generic -- class generic )
    2dup [ classoid? ] [ single-generic? ] bi* and [
        check-method-error
    ] unless ; inline

: remake-single-generic ( generic -- )
    outdated-generics get add-to-unit ;

DEFER: make-generic

: remake-single-generics ( -- )
    outdated-generics get members [ single-generic? ] filter
    [ make-single-generic ] each ;

:: ?single-generic-spec ( generic -- n/var/f )
    generic methods specializers :> ( stack-specs hook-specs )
    hook-specs length 0 = [
        stack-specs length 1 = [ stack-specs first ] [ f ] if
    ] [
        hook-specs length 1 = [
            stack-specs length 0 = [ hook-specs first ] [ f ] if
        ] [ f ] if
    ] if ;

: update-single-generic ( class generic -- )
    [ changed-call-sites ] [ remake-single-generic drop ]
    [ changed-conditionally drop ] 2tri ;

DEFER: define-single-default-method

:: make-generic ( generic -- )
    generic "mathematical" word-prop [
        ! single-math-dispatch
        generic "multi-methods" word-prop [
            [ dup length 1 - swap nth ] dip 
        ] assoc-map generic swap "methods" set-word-prop
        multi-math-combination dup
        generic swap "single-combination" set-word-prop
        generic make-single-generic
        generic swap define-single-default-method
    ] [
        generic ?single-generic-spec dup [
            dup symbol? [
                ! single-hook-dispatch
                :> var
                generic "multi-methods" word-prop [
                    [ dup length 1 - swap nth second ] dip 
                ] assoc-map
                generic swap "methods" set-word-prop
                var <multi-single-hook-combination>
                generic swap "single-combination" set-word-prop
            ] [
                ! standard-single-dispatch
                [| # |
                    generic "multi-methods" word-prop [
                        [ dup length 1 - # - swap nth ] dip 
                 ] assoc-map
                 generic swap "methods" set-word-prop ]
                [
                    <multi-single-standard-combination>
                    generic swap "single-combination" set-word-prop ]
                bi
            ] if
            generic dup "single-combination" word-prop
            generic make-single-generic
            define-single-default-method
        ] [
            ! multi-dispach
            drop
            generic
            [
                [ methods prepare-methods % sort-methods ] keep
                multi-dispatch-quot %
            ] [ ] make generic swap define
        ] if
    ] if ;

! :: make-generic ( generic -- )
!     generic
!     [
!         [ methods prepare-methods % sort-methods ] keep
!         multi-dispatch-quot %
!     ] [ ] make generic swap define ;

: update-generic ( word -- )
    dup "combination-type" word-prop H{ } clone swap method-cache<<
    make-generic ;

! Methods
M: method-body stack-effect
    "multi-method-generic" word-prop stack-effect ;

M: method-body crossref?
    "forgotten" word-prop not ;

M: method-body no-compile? "multi-method-generic" word-prop no-compile? ;

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

GENERIC: implementor-classes ( obj -- class )

M: maybe implementor-classes class>> 1array ;

M: class implementor-classes 1array ;

M: anonymous-union implementor-classes members>> ;

M: anonymous-intersection implementor-classes participants>> ;

: with-implementors ( class generic quot -- )
    [ swap implementor-classes [ implementors-map get at ] map ] dip call ; inline

: with-single-methods ( class generic quot -- )
    [ "methods" word-prop ] prepose [ update-single-generic ] 2bi ; inline

: reveal-single-method ( method classes generic -- )
    [ [ [ adjoin ] with each ] with-implementors ]
    [ [ set-at ] with-single-methods ]
    2bi ;

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
!    dup "multi-methods" word-prop [ drop ] [              ! ???
        [ H{ } clone "multi-methods" set-word-prop ]
        [ "combination-type" word-prop H{ } clone swap method-cache<< ]
        [ update-generic ]
        tri
!    ] if 
;

! Syntax
SYNTAX: MGENERIC: scan-new-word scan-effect 
    parse-variable-effect
    define-generic ;

ERROR: invalid-math-method-parameter ;

M: invalid-math-method-parameter summary
    drop
    "Mathematical multi-method's parameters are two stack parameters of the same class." ;

:: create-method-in ( effect specializer generic -- method )
    generic "mathematical" word-prop [
        specializer [ t [ array? not and ] reduce ] [ length 2 = ] [ first2 = ] tri
        and and [
            invalid-math-method-parameter
        ] unless 
    ] when
    effect specializer generic create-method dup save-location f set-last-word ;

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


! ! ! ! single ! ! ! !

ERROR: no-single-method object generic ;

! ERROR: inconsistent-next-method class generic ;

! TUPLE: multi-single-combination ;

PREDICATE: multi-single-generic < mm-generic
    "single-combination" word-prop multi-single-combination? ;

M: multi-single-generic make-inline cannot-be-inline ;

GENERIC: single-dispatch# ( word -- n )

M: mm-generic single-dispatch# "single-combination" word-prop single-dispatch# ;

SYMBOL: assumed
SYMBOL: default
SYMBOL: generic-word
SYMBOL: single-combination

: with-single-combination ( single-combination quot -- )
     [ single-combination ] dip with-variable ; inline

HOOK: [picker] single-combination ( -- quot )


<PRIVATE

: interesting-class? ( class1 class2 -- ? )
    {
        ! Case 1: no intersection. Discard and keep going
        { [ 2dup classes-intersect? not ] [ 2drop t ] }
        ! Case 2: class1 contained in class2. Add to
        ! interesting set and keep going.
        { [ 2dup class<= ] [ nip , t ] }
        ! Case 3: class1 and class2 are incomparable. Give up
        [ 2drop f ]
    } cond ;

: interesting-classes ( class classes -- interesting/f )
    [ [ interesting-class? ] with all? ] { } make and ;

PRIVATE>

: method-classes ( generic -- classes )
    "methods" word-prop keys ;

: nearest-class ( class generic -- class/f )
    method-classes interesting-classes smallest-class ;

ERROR: method-lookup-failed class generic ;

: ?lookup-method ( class generic -- method/f )
    "methods" word-prop at ;

: lookup-method' ( class generic -- method )
    2dup ?lookup-method [ 2nip ] [ method-lookup-failed ] if* ;

: method-for-object ( obj word -- method )
    [
        [ method-classes [ instance? ] with filter smallest-class ] keep
        ?lookup-method
    ] [ "default-method" word-prop ]
    bi or ;

M: multi-single-combination make-single-default-method
    [ [ [picker] ] dip '[ @ _ no-single-method ] ] with-single-combination ;

! ! ! Build an engine ! ! !

: find-default ( methods -- default )
    ! Side-effects methods.
    [ object bootstrap-word ] dip delete-at* [
        drop generic-word get "default-method" word-prop
    ] unless ;

! 1. Flatten methods
TUPLE: predicate-engine class methods ;

C: <predicate-engine> predicate-engine

: push-method ( method class atomic assoc -- )
    dupd [
        [ ] [ H{ } clone <predicate-engine> ] ?if
        [ methods>> set-at ] keep
    ] change-at ;

: flatten-method ( method class assoc -- )
    over flatten-class [ swap push-method ] 2with with each ;

: flatten-methods ( assoc -- assoc' )
    H{ } clone [ [ swapd flatten-method ] curry assoc-each ] keep ;

! 2. Convert methods
: split-methods ( assoc class -- first second )
    [ [ nip class<= ] curry assoc-reject ]
    [ [ nip class<=     ] curry assoc-filter ] 2bi ;

: convert-methods ( assoc class word -- assoc' )
    over [ split-methods ] 2dip pick assoc-empty?
    [ 3drop ] [ [ execute ] dip pick set-at ] if ; inline

! 2.1 Convert tuple methods
TUPLE: echelon-dispatch-engine n methods ;

C: <echelon-dispatch-engine> echelon-dispatch-engine

TUPLE: tuple-dispatch-engine echelons ;

: push-echelon ( class method assoc -- )
    [ swap dup "layout" word-prop third ] dip
    [ ?set-at ] change-at ;

: echelon-sort ( assoc -- assoc' )
    ! Convert an assoc mapping classes to methods into an
    ! assoc mapping echelons to assocs. The first echelon
    ! is always there
    H{ { 0 f } } clone [ [ push-echelon ] curry assoc-each ] keep ;

: copy-superclass-methods ( engine superclass assoc -- )
    at* [ [ methods>> ] bi@ assoc-union! drop ] [ 2drop ] if ;

: copy-superclasses-methods ( class engine assoc -- )
    [ superclasses-of ] 2dip
    [ swapd copy-superclass-methods ] 2curry each ;

: convert-tuple-inheritance ( assoc -- assoc' )
    ! A method on a superclass A might have a higher precedence
    ! than a method on a subclass B, if the methods are
    ! defined on incomparable classes that happen to contain
    ! A and B, respectively. Copy A's methods into B's set so
    ! that they can be sorted and selected properly.
    dup dup [ copy-superclasses-methods ] curry assoc-each ;

: <tuple-dispatch-engine> ( methods -- engine )
    convert-tuple-inheritance echelon-sort
    [ dupd <echelon-dispatch-engine> ] assoc-map
    tuple-dispatch-engine boa ;

: convert-tuple-methods ( assoc -- assoc' )
    tuple bootstrap-word
    \ <tuple-dispatch-engine> convert-methods ;

! 3 Tag methods
TUPLE: tag-dispatch-engine methods ;

C: <tag-dispatch-engine> tag-dispatch-engine

: <engine> ( assoc -- engine ) 
    flatten-methods
    convert-tuple-methods
    <tag-dispatch-engine> ;

! ! ! Compile engine ! ! !
GENERIC: compile-engine ( engine -- obj )

: compile-engines ( assoc -- assoc' )
    [ compile-engine ] assoc-map ;

: compile-engines* ( assoc -- assoc' )
    [ over assumed [ compile-engine ] with-variable ] assoc-map ;

: direct-dispatch-table ( assoc n -- table )
    default get <array> <enumerated> swap assoc-union! seq>> ;

: tag-number ( class -- n ) "type" word-prop ;

M: tag-dispatch-engine compile-engine
    methods>> compile-engines*
    [ [ tag-number ] dip ] assoc-map
    num-types get direct-dispatch-table ;

: build-fast-hash ( methods -- buckets )
    >alist V{ } clone [ hashcode 1array ] distribute-buckets
    [ compile-engines* >alist concat ] map ;

M: echelon-dispatch-engine compile-engine
    dup n>> 0 = [
        methods>> dup assoc-size {
            { 0 [ drop default get ] }
            { 1 [ >alist first second compile-engine ] }
        } case
    ] [
        methods>> compile-engines* build-fast-hash
    ] if ;

M: tuple-dispatch-engine compile-engine
    tuple assumed [
        echelons>> compile-engines
        dup keys supremum 1 + f <array>
        <enumerated> swap assoc-union! seq>>
    ] with-variable ;

PREDICATE: predicate-engine-word < word "owner-generic" word-prop ;

SYMBOL: predicate-engines

: sort-single-methods ( assoc -- assoc' )
    >alist [ keys sort-classes ] keep extract-keys ;

: quote-methods ( assoc -- assoc' )
    [ 1quotation \ drop prefix ] assoc-map ;

: find-predicate-engine ( classes -- word )
    predicate-engines get [ at ] curry map-find drop ;

: next-predicate-engine ( engine -- word )
    class>> superclasses-of
    find-predicate-engine
    default get or ;

: methods-with-default ( engine -- assoc )
    [ methods>> clone ] [ next-predicate-engine ] bi
    object bootstrap-word pick set-at ;

: keep-going? ( assoc -- ? )
    assumed get swap second first class<= ;

ERROR: unreachable ;

: prune-redundant-predicates ( assoc -- default assoc' )
    {
        { [ dup empty? ] [ drop [ unreachable ] { } ] }
        { [ dup length 1 = ] [ first second { } ] }
        { [ dup keep-going? ] [ rest-slice prune-redundant-predicates ] }
        [ [ first second ] [ rest-slice ] bi ]
    } cond ;

: class-predicates ( assoc -- assoc )
    [ [ predicate-def [ dup ] prepend ] dip ] assoc-map ;

: <predicate-engine-word> ( -- word )
    generic-word get name>> "/predicate-engine" append f <word>
    dup generic-word get "owner-generic" set-word-prop ;

M: predicate-engine-word stack-effect "owner-generic" word-prop stack-effect ;

: define-predicate-engine ( alist -- word )
    [ <predicate-engine-word> ] dip
    [ define ] [ drop generic-word get "engines" word-prop push ] [ drop ] 2tri ;

: compile-predicate-engine ( engine -- word )
    methods-with-default
    sort-single-methods
    quote-methods
    prune-redundant-predicates
    class-predicates
    [ last ] [ alist>quot [picker] prepend define-predicate-engine ] if-empty ;

M: predicate-engine compile-engine
    [ compile-predicate-engine ] [ class>> ] bi
    [ drop ] [ predicate-engines get set-at ] 2bi ;

M: word compile-engine ;

M: f compile-engine ;

: build-decision-tree ( generic -- methods )
    [ "engines" word-prop forget-all ]
    [ V{ } clone "engines" set-word-prop ]
    [
        "methods" word-prop clone
        [ find-default default set ]
        [ <engine> compile-engine ] bi
    ] tri ;

HOOK: inline-cache-quots single-combination
        ( word methods -- pic-quot/f pic-tail-quot/f )

M: multi-single-combination inline-cache-quots 2drop f f ;

: define-inline-cache-quot ( word methods -- )
    [ drop ] [ inline-cache-quots ] 2bi
    [ >>pic-def ] [ >>pic-tail-def ] bi*
    drop ;

HOOK: mega-cache-quot single-combination ( methods -- quot/f )

M: multi-single-combination perform-combination
    [
        H{ } clone predicate-engines set
        dup generic-word set
        dup build-decision-tree
        [ "decision-tree" set-word-prop ]
        [ mega-cache-quot define ]
        [ define-inline-cache-quot ]
        2tri
    ] with-single-combination ;

M: multi-single-generic effective-method
    [ get-datastack ] dip
    [ "single-combination" word-prop #>> swap <reversed> nth ] keep
    method-for-object ;


PREDICATE: default-method < word "default" word-prop ;

: single-method-word-props ( class generic -- assoc )
    [
        "method-generic" ,,
        "method-class" ,,
    ] H{ } make ;

: single-method-word-name ( class generic -- string )
    [ class-name ] [ name>> ] bi* "=>" glue ;

M: method-body parent-word
    "multi-method-generic" word-prop ;

: <single-method> ( class generic -- method )
    check-single-method
    [ method-word-name f <word> ] [ single-method-word-props ] 2bi
    >>props ;

:: <single-default-method> ( generic combination -- method )
    generic combination
    [ drop object bootstrap-word swap <single-method> ] [ make-single-default-method ] 2bi
    [ define ] [ drop t "default" set-word-prop ] [ drop ] 2tri
    dup generic "declared-effect" word-prop "declared-effect" set-word-prop ;

: define-single-default-method ( generic combination -- )
    dupd <single-default-method> "default-method" set-word-prop ;

: define-single-generic ( word combination effect -- )
    [ [ check-combination-effect ] keep set-stack-effect ]
    [
        drop
        2dup [ "single-combination" word-prop ] dip = [ 2drop ] [
            {
                [ drop reset-generic ]
                [ "single-combination" set-word-prop ]
                [ drop H{ } clone "methods" set-word-prop ]
                [ define-single-default-method ]
            }
            2cleave
        ] if ]
    [ 2drop remake-single-generic ] 3tri ;



! ! ! ! standard ! ! ! !

M: multi-single-standard-combination check-combination-effect
    [ single-dispatch# ] [ in>> length ] bi* over >
    [ drop ] [ bad-dispatch-position ] if ;

PREDICATE: multi-single-standard-generic < mm-generic
    "single-combination" word-prop multi-single-standard-combination? ;

PREDICATE: multi-single-simple-generic < multi-single-standard-generic
    "single-combination" word-prop #>> 0 = ;

CONSTANT: multi-single-simple-combination
    T{ multi-single-standard-combination f 0 }

: define-multi-single-simple-generic ( word effect -- )
    [ multi-single-simple-combination ] dip define-single-generic ;

M: multi-single-standard-combination [picker]
    single-combination get #>> picker ;

M: multi-single-standard-combination single-dispatch# #>> ;

M: multi-single-standard-generic effective-method
    [ get-datastack ] dip [ "single-combination" word-prop #>> swap <reversed> nth ] keep
    method-for-object ;

: inline-cache-quot ( word methods miss-word -- quot )
    [ [ literalize , ] [ , ] [ single-combination get #>> , { } , , ] tri* ] [ ] make ;

M: multi-single-standard-combination inline-cache-quots
    ! Direct calls to the generic word (not tail calls or indirect calls)
    ! will jump to the inline cache entry point instead of the megamorphic
    ! dispatch entry point.
    [ \ inline-cache-miss inline-cache-quot ]
    [ \ inline-cache-miss-tail inline-cache-quot ]
    2bi ;

: make-empty-cache ( -- array )
    mega-cache-size get f <array> ;

M: multi-single-standard-combination mega-cache-quot
     single-combination get #>> make-empty-cache \ mega-cache-lookup [ ] 4sequence ;


! ! ! ! hook ! ! ! !

PREDICATE: multi-single-hook-generic < mm-generic
    "single-combination" word-prop multi-single-hook-combination? ;

M: multi-single-hook-combination [picker]
    single-combination get var>> [ get ] curry ;

M: multi-single-hook-combination single-dispatch# drop 0 ;

M: multi-single-hook-combination mega-cache-quot
    1quotation [picker] [ lookup-method (execute) ] surround ;

! M: multi-single-hook-generic definer drop \ HOOK: f ;

M: multi-single-hook-generic effective-method
    [ "single-combination" word-prop var>> get ] keep method-for-object ;


! ! ! ! math ! ! ! !

PREDICATE: multi-math-class < class
    dup null bootstrap-word eq? [
        drop f
    ] [
        number bootstrap-word class<=
    ] if ;

<PRIVATE

: bootstrap-words ( classes -- classes' )
    [ bootstrap-word ] map ;

: math-precedence ( class -- pair )
    [
        { fixnum integer rational real number object } bootstrap-words
        swap [ swap class<= ] curry find drop -1 or
    ] [
        { fixnum bignum ratio float complex object } bootstrap-words
        swap [ class<= ] curry find drop -1 or
    ] bi 2array ;

: (math-upgrade) ( max class -- quot )
    dupd = [ drop [ ] ] [ "coercer" word-prop [ ] or ] if ;

PRIVATE>

: math-class-max ( class1 class2 -- class )
    [ [ math-precedence ] bi@ after? ] most ;

: math-upgrade ( class1 class2 -- quot )
    [ math-class-max ] 2keep [ (math-upgrade) ] bi-curry@ bi
    [ dup empty? [ [ dip ] curry ] unless ] dip [ ] append-as ;

ERROR: no-multi-math-method left right generic ;

: default-multi-math-method ( generic -- quot )
    [ no-multi-math-method ] curry [ ] like ;

<PRIVATE

: (math-method) ( generic class -- quot )
    over ?lookup-method
    [ 1quotation ]
    [ default-multi-math-method ] ?if ;

PRIVATE>

: object-method ( generic -- quot )
    object bootstrap-word (math-method) ;

: multi-math-method ( word class1 class2 -- quot )
    2dup and [
        [ 2array [ declare ] curry nip ]
        [ math-upgrade nip ]
        [ math-class-max over nearest-class (math-method) ]
        3tri 3append
    ] [
        2drop object-method
    ] if ;

<PRIVATE

: make-math-method-table ( classes quot: ( ... class -- ... quot ) -- alist )
    [ bootstrap-words ] dip [ keep swap ] curry { } map>assoc ; inline

: math-alist>quot ( alist -- quot )
    [ generic-word get object-method ] dip alist>quot ;

: tag-dispatch-entry ( tag picker -- quot )
    [ "type" word-prop 1quotation [ tag ] [ eq? ] surround ] dip prepend ;

: tag-dispatch ( picker alist -- alist' )
    swap [ [ tag-dispatch-entry ] curry dip ] curry assoc-map math-alist>quot ;

: tuple-dispatch-entry ( class picker -- quot )
    [ 1quotation [ { tuple } declare class-of ] [ eq? ] surround ] dip prepend ;

: tuple-dispatch ( picker alist -- alist' )
    swap [ [ tuple-dispatch-entry ] curry dip ] curry assoc-map math-alist>quot ;

: math-dispatch-step ( picker quot: ( ... class -- ... quot ) -- quot )
    [ { bignum float fixnum } swap make-math-method-table ]
    [ { ratio complex } swap make-math-method-table tuple-dispatch ] 2bi
    tuple swap 2array prefix tag-dispatch ; inline

: fixnum-optimization ( word quot -- word quot' )
    [ dup fixnum bootstrap-word dup multi-math-method ]
    [
        ! remove redundant fixnum check since we know
        ! both can't be fixnums in this branch
        dup length 3 - cut unclip
        [ length 2 - ] [ nth ] bi prefix append
    ] bi*
    [ if ] 2curry [ 2dup both-fixnums? ] prepend ;

PRIVATE>


M: multi-math-combination make-single-default-method
    drop default-multi-math-method ;

M: multi-math-combination perform-combination
    drop dup generic-word [
        dup [ over ] [
            dup multi-math-class? [
                [ dup ] [ multi-math-method ] 2with math-dispatch-step
            ] [
                drop object-method
            ] if
        ] with math-dispatch-step
        fixnum-optimization
        define
    ] with-variable ;

PREDICATE: multi-math-generic < mm-generic
    "single-combination" word-prop multi-math-combination? ;

! M: math-generic definer drop \ MATH: f ;
