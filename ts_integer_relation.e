note
	explicit: wrapping, contracts

class
	TS_INTEGER_RELATION

inherit

	ANY
		redefine
			is_equal
		end

create
	make_empty

feature -- Initialization

	make_empty
		note
			status: creator
		require
		do
			create data
			wrap
		ensure
			is_wrapped
			is_empty
		end


feature -- Data access

	count: INTEGER
			-- How many pairs are currently stored
		require
			closed
		do
			Result := data.count
		ensure
			Result = data.sequence.count
		end

	remove (a_left, a_right: INTEGER)
		require
			is_wrapped
		local
			i: INTEGER
		do
			from
				i := 1
			invariant
				is_wrapped
				across 1 |..| (i - 1) as j all not data.sequence [j.item].same_values (a_left, a_right) end
			variant
				data.sequence.count - i
			until
				i > data.count
			loop
				if data [i].same_values (a_left, a_right) then
					unwrap
					data.remove_at (i)
					wrap
					i := i - 1
				end
				i := i + 1
			end
		ensure
			not has (a_left, a_right)
				-- TODO: redo postocondition with subset
--			old has (a_left, a_right) implies old data.sequence.range.difference (data.sequence.range).count > 0
--			old has (a_left, a_right) implies old data.sequence.range.difference (data.sequence.range).any_item.same_values (a_left, a_right)
--			not old has (a_left, a_right) implies data.sequence = old data.sequence
			is_wrapped
		end

--	add_pair (a_pair: TS_INTEGER_PAIR)
--		require
--			wrapped: is_wrapped
--			pair_not_void: a_pair /= Void
--		local
--			l_left, l_right: INTEGER
--		do
--			l_left := a_pair.left
--			l_right := a_pair.right
--			check same_pair: a_pair.same_values (l_left, l_right) end
--			add (l_left, l_right)
--			check added: has (l_left, l_right) end
--		ensure
--			is_wrapped
--			has (a_pair.left, a_pair.right)
--			has_pair (a_pair)
--		end

	add (a_left, a_right: INTEGER)
		require
			is_wrapped
		do
			if not has (a_left, a_right) then
				unwrap
				data.extend_back (create {TS_INTEGER_PAIR}.make (a_left, a_right))
				wrap
			end
		ensure
			is_wrapped
			old has (a_left, a_right) implies sequence = old sequence
			old has (a_left, a_right) implies is_equal (old Current)
			(not old has (a_left, a_right)) implies (sequence.but_last = old sequence and sequence.last.same_values (a_left, a_right))
				-- TODO: redo postocondition with subset
			has (a_left, a_right)
			across data.sequence as s some s.item.same_values (a_left, a_right)  end
		end

	is_empty: BOOLEAN
		require
			closed
		do
			Result := data.is_empty
		ensure
			closed
			Result = data.sequence.is_empty
			Result = (data.sequence.count = 0)
		end

	has (a_left, a_right: INTEGER): BOOLEAN
		require
			closed
		do
			Result := list_has (data, a_left, a_right)
		ensure
			closed
			is_empty implies not Result
			Result = across data.sequence as s some s.item.same_values (a_left, a_right) end
		end

	has_pair (a_pair: TS_INTEGER_PAIR): BOOLEAN
		require
			a_pair /= Void
			closed
		do
			Result := has (a_pair.left, a_pair.right)
		ensure
			closed
			Result = has (a_pair.left, a_pair.right)
			Result = across data.sequence as s some s.item.is_equal (a_pair)  end
		end

	list_has (a_list: V_LINKED_LIST [TS_INTEGER_PAIR]; a_left, a_right: INTEGER): BOOLEAN
		require
			a_list /= Void
			a_list.closed
			a_list.sequence.non_void
		do
			Result := list_find (a_list, a_left, a_right) > 0
		ensure
			Result = across a_list.sequence as s some s.item.same_values (a_left, a_right) end
		end

feature -- Data storage

	data: V_LINKED_LIST [TS_INTEGER_PAIR]

	occurences_count (a_left, a_right: INTEGER): INTEGER
		note
			status: ghost
		require
			data.sequence.non_void
		do
			if data.sequence.is_empty then
				Result := 0
			else
				Result := occurences_count_before (a_left, a_right, data.sequence.count)
			end
		ensure
			data.sequence.is_empty implies Result = 0
			not data.sequence.is_empty implies Result = occurences_count_before (a_left, a_right, data.sequence.count)
		end

	occurences_count_before (a_left, a_right, a_v: INTEGER): INTEGER
			-- How many times <a_left, a_right> appeared in `data' list
			-- at positions <= `a_v'?
		note
			status: ghost
		require
			decreases (a_v)
			1 <= a_v and a_v <= data.sequence.count
			data.sequence.non_void
		do
			if data.sequence [a_v].same_values (a_left, a_right) then
				Result := 1
			else
				Result := 0
			end
			if a_v > 1 then
				Result := Result + occurences_count_before (a_left, a_right, a_v - 1)
			end
		ensure
			(a_v = 1) implies (Result = if data.sequence [1].same_values (a_left, a_right) then 1 else 0 end)
			(a_v > 1) implies (Result = occurences_count_before (a_left, a_right, a_v - 1) + if data.sequence [a_v].same_values (a_left, a_right) then 1 else 0 end)
		end

feature -- Comparison

	is_subset_of (a_other: TS_INTEGER_RELATION): BOOLEAN
		require
			closed
			a_other.closed
		local
			i: INTEGER
			k: INTEGER
		do
			Result := True
			from
				i := 1
			invariant
				Result implies across 1 |..| (i - 1) as j all a_other.has_pair (data.sequence [j.item]) end
				Result implies k = 0
				(not Result) implies across 1 |..| (i - 1) as j some not a_other.has_pair (data.sequence [j.item]) end
				(not Result) implies (1 <= k and k <= data.sequence.count)
				(not Result) implies not a_other.has_pair (data.sequence [k])
			variant
				data.sequence.count - i
			until
				i > data.count or not Result
			loop
				if not a_other.has_pair (data [i]) then
					check
						not a_other.has_pair (data.sequence [i])
					end
					Result := False
					k := i
				end
				i := i + 1
			end
		ensure
			closed
			a_other.closed
			is_empty implies Result
			a_other.is_empty implies (Result = is_empty)
			Result implies across data.sequence as s all a_other.has_pair (s.item) end
			(not Result) implies across 1 |..| (data.sequence.count) as j some not a_other.has_pair (data.sequence [j.item]) end
		end

	is_equal (a_other: TS_INTEGER_RELATION): BOOLEAN
		require else
			closed
			a_other.closed
		do
			Result := Current.is_subset_of (a_other) and a_other.is_subset_of (Current)
		ensure then
			Result = (Current.is_subset_of (a_other) and a_other.is_subset_of (Current))
		end

feature -- Verification and Utils

	sequence: MML_SEQUENCE [TS_INTEGER_PAIR]
		note
			status: ghost
		attribute
		end

	find (a_left, a_right: INTEGER): INTEGER
		require
			closed
		do
			Result := list_find (data, a_left, a_right)
		ensure
			closed
			found_the_only: (Result > 0) implies (across 1 |..| data.sequence.count as i all (i.item /= Result) = (not data.sequence [i.item].same_values (a_left, a_right)) end)
		end

	list_find (a_list: V_LINKED_LIST [TS_INTEGER_PAIR]; a_left, a_right: INTEGER): INTEGER
		require
			a_list /= Void
			a_list.closed
			a_list.sequence.non_void
		local
			l_found: BOOLEAN
		do
			from
				Result := 1
				l_found := False
			invariant
				true_result_definition: l_found implies a_list.sequence [Result - 1].same_values (a_left, a_right)
				false_result_definition: not l_found implies across 1 |..| (Result - 1) as j all not a_list.sequence [j.item].same_values (a_left, a_right) end
			variant
				a_list.sequence.count - Result
			until
				l_found or Result > a_list.count
			loop
				l_found := a_list [Result].same_values (a_left, a_right)
				Result := Result + 1
			end
			if l_found then
				Result := Result - 1
			else
				Result := 0
			end
		ensure
			Result <= a_list.sequence.count
			0 <= Result
			(Result = 0) = (across a_list.sequence as s all not s.item.same_values (a_left, a_right) end)
			(Result > 0) = (across a_list.sequence as s some s.item.same_values (a_left, a_right) end)
			(Result > 0) implies (a_list.sequence [Result].same_values (a_left, a_right))
		end

invariant
	data /= Void
	owns = ({like owns} [[data]]).union (sequence.range)
	sequence = data.sequence
	sequence_non_void: sequence.non_void
	data.sequence.non_void
	across 1 |..| sequence.count as i all across 1 |..| sequence.count as j all (i.item = j.item) = (sequence [i.item].is_equal (sequence [j.item])) end end
	data.observers.is_empty

end
