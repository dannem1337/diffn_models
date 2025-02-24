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

%% Parameters
int: n; % number of different products
array[1..4] of int: shelves; % dimensions length, width, height and number of shelves
array[1..n, 1..4] of int: products; % dimensions length, width, height and number of the same products

%% Derived Parameters
% Total number of shelves
int: no_shelves = shelves[4];
% Number of each product
array [1..n] of int: no_products = products[..,4];
% Total number of products
int: total_products = sum(products[..,4]);
% All product sizes
array[1..total_products, 1..3] of int: product_sizes = array2d(1..total_products, 1..3,
        [
            [products[i,1], products[i,2], products[i,3]][x] 
            | i in 1..n, _ in 1..no_products[i], x in 1..3
        ]);
% Largest size im the products list
int: largest_product_size = max(i in 1..n, j in 1..3) (products[i,j]);

%% Descision Variables
%  The size of each product is its size if it is in the shelf and [0, 0, 0] if it is not 
array[1..total_products, 1..3, 1..no_shelves] of var 0..largest_product: product_sizes_3d::add_to_output;
% Product j is placed on shelf product_placement[j]
array[1..total_products] of var 1..no_shelves: product_placement::add_to_output;
% Starting positions of each product in each shelf
array[1..total_products, 1..3, 1..no_shelves] of var 1..max(shelves[1..3]): startXYZ::add_to_output;
% The number of shelves used
var 1..no_shelves: no_loaded_shelves::add_to_output;

% Sets all rows in products_sizes_3d to their respective sizes if they exist in 
% shelf i and [0, 0, 0] if they do not exist in shelf i
constraint forall(i in 1..no_shelves) 
    (
        forall(j in 1..total_products) 
        (
            if product_placement[j] == i 
            then product_sizes_3d[j,.., i] = product_sizes[j,..]
            else product_sizes_3d[j,.., i] = [0, 0, 0] endif
        )
    );

% Constrains all products in each shelf to no overlap, nonstrict is used so
% that we do not include products which are not in that shelf (they have sizes
% [0, 0, 0])
constraint forall(i in 1..no_shelves)
    ( 
        diffn_nonstrict_k
        (
            startXYZ[.., .., i],
            product_sizes_3d[.., .., i]
        )
    );

% The number of loaded shelves is the max product_placement, this will also force
% shelves to be filled in ascending order, starting from 1
constraint no_loaded_shelves = max(product_placement);

% The products must be placed such that they are contained within the dimensions of 
% the shelf
constraint forall(i in 1..no_shelves) 
    (
        forall (j in 1..total_products) 
        (
            startXYZ[j, 1, i] + product_sizes[j, 1] <= shelves[1] + 1 /\
            startXYZ[j, 2, i] + product_sizes[j, 2] <= shelves[2] + 1 /\
            startXYZ[j, 3, i] + product_sizes[j, 3] <= shelves[3] + 1
        )
    );

solve minimize no_loaded_shelves;
