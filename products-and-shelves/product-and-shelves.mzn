%% Problem description:
% In a warehouse, a number of products are to be placed on some shelves such that
% the the minimum amount of shelves are used. These products are all shaped like
% 3-dimensional boxes, with dimensions length, width and height. The shelves are
% also shaped like 3-dimensional with dimensions length, width and height and the
% number of shelves are finite. Neither the shelf or the products are allowed to be rotated.
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

include "diffn_nonstrict_k.mzn";

% Dimensions considered
enum Dimension = {Length, Width, Height};

%% Parameters
enum Product;

% Space available on each shelf in all dimensions
array[Dimension] of int: shelves;
% Space required for each product in all dimensions
array[Product, Dimension] of int: product_size;
% Total number of shelves
int: no_shelves;

%% Derived Parameters
enum Shelf = S(1..no_shelves);
% Number of each product
array [Product] of int: no_products;
% Enumeration of all items (of all type products)
enum Item = I(1..sum(no_products));
% Mapping each item to its product
array[Item] of Product: product = array1d(Item, [
	p | p in Product, _ in 1..no_products[p]
]);

%% Descision Variables
%  The size of each product is its size if it is in the shelf and [0, 0, 0] if it is not
array[Item, Dimension, Shelf] of var 0..max(product_size): item_shelve_size ::output;
% Product j is placed on shelf item_shelving[j]
array[Item] of var Shelf: item_shelving ::output;
% Starting positions of each product in each shelf
array[Item, Dimension, Shelf] of var 1..max(shelves): item_shelve_placement ::output;
% The number of loaded shelves is the max item_shelving, this will also force
% shelves to be filled in ascending order, starting from 1
var Shelf: last_loaded_shelf ::output = max(item_shelving);

% Sets all rows in products_sizes_3d to their respective sizes if they exist in
% shelf i and [0, 0, 0] if they do not exist in shelf i
constraint forall(s in Shelf, it in Item, p = product[it]) (
	if item_shelving[it] == s then
		item_shelve_size[it,.., s] = product_size[p,..]
	else
		item_shelve_size[it,.., s] = [0, 0, 0]
	endif
);

% Constrains all products in each shelf to no overlap, nonstrict is used so
% that we do not include products which are not in that shelf (they have sizes
% [0, 0, 0])
constraint forall(s in Shelf) (
	diffn_nonstrict_k(item_shelve_placement[.., .., s], item_shelve_size[.., .., s])
);

% The products must be placed such that they are contained within the dimensions of
% the shelf
constraint forall(s in Shelf, it in Item, d in Dimension) (
  item_shelve_placement[it, d, s] + item_shelve_size[it, d, s] <= shelves[d] + 1
);

solve minimize last_loaded_shelf;
