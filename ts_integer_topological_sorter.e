note
	explicit: wrapping, contracts

class
	TS_INTEGER_TOPOLOGICAL_SORTER

inherit
	TS_INTEGER_RELATION
		redefine
			make_empty
		end

create
	make_empty

feature -- Initialization

	make_empty
		note
			status: creator
		local
			i: INTEGER
		do
			Precursor
			create sorted
			wrap
		ensure then
			is_empty
			sorted.is_empty
		end

feature -- Topological Sort

	sorted: V_LINKED_LIST[INTEGER]
		-- Result of last sorting. If cycle was detected, then
		-- this list contains only subset of range.
		-- Run sorting by calling `topsort'

	fully_sorted: BOOLEAN
		-- Was last sorting successful? I.e. no cycles were detected.
		-- Run sorting by calling `topsort'	

	topsort
		require
			is_wrapped
		local
			s: INTEGER
			l_start: TS_INTEGER_PAIR
		do
			unwrap
			create sorted
			fully_sorted := False
			wrap
			from
			invariant
				is_wrapped
			variant
				count
			until
				not has_more_starts
			loop
				l_start := get_start
				unwrap
				sorted.extend_back (l_start.right)
				wrap
				remove_outgoing_from (l_start.right)
			end
			unwrap
			fully_sorted := is_empty
			wrap
		ensure
			is_wrapped
			not has_more_starts
			fully_sorted = is_empty
		end

	is_start (a_left, a_right: INTEGER): BOOLEAN
		require
			has (a_left, a_right)
		do
			Result := not has_incoming (a_left, a_right)
		ensure
			Result = across data.sequence as s all s.item.right /= a_left end
		end

	get_start: TS_INTEGER_PAIR
		require
			closed
			has_more_starts
		local
			p: TS_INTEGER_PAIR
			i: INTEGER
		do
			i := find_start_index
			check 1 <= i and i <= data.sequence.count end
			check 1 <= i and i <= data.count end
			p := data[i]
			create Result.make (p.left, p.right)
		ensure
			is_start (Result.left, Result.right)
		end

	has_more_starts: BOOLEAN
		require
			closed
		do
			Result := find_start_index > 0
		ensure
			Result = across data.sequence as s some is_start (s.item.left, s.item.right) end
		end

	remove_outgoing_from (a_left: INTEGER)
		require
			is_wrapped
		local
			i: INTEGER
		do
			from
				i := 1
			invariant
				is_wrapped
				across 1 |..| (i - 1) as j all data.sequence [j.item].left /= a_left end
			variant
				data.sequence.count - i
			until
				i > data.count
			loop
				if data [i].left = a_left then
					unwrap
					data.remove_at (i)
					wrap
					i := i - 1
				end
				i := i + 1
			end
		ensure
--			not has (a_left, a_right)
			-- TODO: redo postocondition with subset
			across old sequence as s all has_pair(s.item) = (s.item.left =  a_left) end
			is_subset_of(old Current)
			is_wrapped
		end


feature {NONE} -- Topological Sort (helper functions)

	has_incoming (a_left, a_right: INTEGER): BOOLEAN
		require
			closed
			has (a_left, a_right)
		local
			i: INTEGER
		do
			from
				i := 1
			invariant
				Result = across 1 |..| (i - 1) as j some data.sequence[j.item].right = a_left end
				Result implies data.sequence[i - 1].right = a_left
			variant
				data.sequence.count - i
			until
				i > data.count or Result
			loop
				if data[i].right = a_left then
					Result := True
				end
				i := i + 1
			end
		ensure
			Result = across data.sequence as s some s.item.right = a_left end
		end

	find_start_index: INTEGER
		-- Index of some
		require
			closed
		local
			i: INTEGER
			l_found: BOOLEAN
		do
			from
				i := 1
			invariant
				l_found = (i > 1 and then not has_incoming (data.sequence[i - 1].left, data.sequence[i - 1].right))
				across 1 |..| (i - 2) as j all has_incoming (data.sequence[j.item].left, data.sequence[j.item].right) end
			variant
				data.sequence.count - i
			until
				i > data.count or l_found
			loop
				check not l_found end
				if not has_incoming (data[i].left, data[i].right) then
					l_found := True
				end
				i := i + 1
			end
			if l_found then
				Result := i - 1
			end
		ensure
			(0 <= Result and Result <= data.sequence.count)
			(Result = 0) = (across data.sequence as s all has_incoming (s.item.left, s.item.right) end)
			(Result > 0) = (Result > 0 and then not has_incoming (data.sequence[Result].left, data.sequence[Result].right))
			across data.sequence as s some not has_incoming (s.item.left, s.item.right) end implies Result > 0
		end

invariant
	sorted /= Void

	owns[sorted]

end
