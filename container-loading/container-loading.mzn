%% Problem Description
% Given a container of fixed length, width and height. Packages shaped like
% 3-dimensional boxes are to be placed in the container such that none overlap
% and their area is minmized. The area is calculated by multiplying the length,
% width and height of the placed packages. Rotations of the packages and the
% container is not allowed.
%
%            +--------------+
%           /|             /|
%          / |            / |
%         *--+-----------*  |
%         |  |           |  |
% height->|  |           |  |
%         |  |           |  |
%         |  +-----------+--+
%         | / <-width    | /
%         |/             |/
%         *--------------*
%             length^

include "diffn_k.mzn";
include "lex_chain_lesseq.mzn";

% Dimensions considered
enum Dimension = {Length, Width, Height};

%% Parameters
array[Dimension] of int: container_size;
enum Box;
array[Box] of int: no_boxes;
array[Box, Dimension] of int: box_size;

constraint forall(b1, b2 in Box where b1 < b2)(
	assert(box_size[b1,..] != box_size[b2,..], "Boxes \(b1) and \(b2) have the same size and should therefore be combined")
);

%% Derived Parameters
% Individual boxes and their mapping to their type
enum Item = I(1..sum(no_boxes));
array[Item] of Box: box_map = [b | b in Box, _ in 1..no_boxes[b]];
array[Item, Dimension] of int: item_size = [(i,d): box_size[box_map[i], d] | i in Item, d in Dimension];

%% Descision Variables
% Positions of individual boxes in each dimension
% (Note that their domain restricts them to be within the container's dimensions)
array[Item, Dimension] of var int: start_pos ::output = [
	(i, d): let {
		var 0..(container_size[d] - item_size[i, d]): pos
	} in pos
	| i in Item, d in Dimension
];

% Find the size of the minimal used rectangular cuboid
array[Dimension] of var int: used_size ::output = [
	max([start_pos[i, d] + item_size[i, d] | i in Item])
	| d in Dimension
];

%% Constraints
% None of the boxes can be overlapping
constraint diffn_k(start_pos, item_size);

% Force a lexicographic ordering of the boxes of the same size
constraint symmetry_breaking_constraint(
	forall(b in Box) (
		let {
			any: x = [start_pos[i, d] | i in Item where box_map[i] = b, d in Dimension];
			array[int, Dimension] of var int: coord = array2d(1..length(x) div 3, Dimension, x);
		} in lex_chain_lesseq(coord)
	)
);

solve minimize product(used_size);
