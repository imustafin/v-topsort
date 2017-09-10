note
	model: pairs, relation, lower, upper


class
	TS_INTEGER_RELATION


create
	make_empty

feature -- Initialization

	make_empty(a_lower, a_upper: INTEGER)
		do
			create data
			relation := {MML_RELATION[INTEGER, INTEGER]}.empty_relation
			set_owns ({like owns} [[data]])
			lower := a_lower
			upper := a_upper
		ensure
			lower = a_lower
			upper = a_upper
			is_empty
		end

feature -- Storage

	lower, upper: INTEGER
		-- Relation is between integers which are in
		-- range [`lower', `upper']

	data: V_LINKED_LIST[TS_INTEGER_PAIR]

feature -- Usage

	is_empty: BOOLEAN
		do
			Result := data.is_empty
		ensure
			consistent_with_pairs: Result = pairs.is_empty
--			consistent_with_relation: Result = relation.is_empty
		end

	has (a_left, a_right: INTEGER): BOOLEAN
		local
			i: INTEGER
		do
			from
				i := 1
			invariant
				res_def: Result implies pairs[i - 1].same_values (a_left, a_right)
				not_res_def: (not Result) implies across 1 |..| (i - 1) as j all not pairs[j.item].same_values (a_left, a_right)  end
			variant
				pairs.count - i
			until
				i > data.count or Result
			loop
				if data[i].same_values (a_left, a_right) then
					Result := True
				end
				i := i + 1
			end
		ensure
			consistent_with_data: Result = across pairs as p some p.item.same_values (a_left, a_right)  end
--			consistent_with_relation: Result = relation.has (a_left, a_right)
		end

feature -- Verfication

	pairs: MML_SEQUENCE [TS_INTEGER_PAIR]
		note
			status: ghost
		attribute
		end

	relation: MML_RELATION[INTEGER, INTEGER]
		note
			status: ghost
		attribute
		end

	pair_in_range (a_pair: TS_INTEGER_PAIR): BOOLEAN
		note
			status: functional
		require
			a_pair /= Void
			reads (a_pair)
			reads_field(["lower", "upper"], Current)
		do
			Result := value_in_range (a_pair.left) and value_in_range (a_pair.right)
		end

	value_in_range (a_value: INTEGER): BOOLEAN
		note
			status: ghost, functional
		require
			reads_field(["lower", "upper"], Current)
		do
			Result := lower <= a_value and a_value <= upper
		end

	pairs_has_pair (a_left, a_right: INTEGER): BOOLEAN
		note
			status: ghost
			explicit: "all"
		require
			inv_without("relation_in_pairs")
		local
			i: INTEGER
		do
			from
				i := 1
			invariant
				not_res_def: (not Result) implies across 1 |..| (i - 1) as j all not pairs[j.item].same_values (a_left, a_right) end
				res_def: Result implies pairs[i - 1].same_values (a_left, a_right)
			variant
				pairs.count - i
			until
				i > pairs.count or Result
			loop
				Result := pairs[i].same_values (a_left, a_right)
				i := i + 1
			end
		ensure
			Result = across pairs as p some p.item.same_values (a_left, a_right) end
		end

invariant

	data_exists: data /= Void

	owns_data: owns[data] -- for pairs_def
	pairs_def: pairs = data.sequence

	owns_def: owns = {like owns} [[data]] + pairs.range
	pairs_exist: pairs.non_void

	pairs_in_range: across pairs as p all pair_in_range (p.item) end

	pairs_in_relation: across pairs as p all relation.has (p.item.left, p.item.right) end
--	relation_in_pairs: across relation.to_set as r all pairs_has_pair (r.item.left, r.item.right) end
	realtion_in_pairs: across relation.to_set as r all
		across pairs as p some p.item.same_values (r.item.left, r.item.right)  end
	end

end
