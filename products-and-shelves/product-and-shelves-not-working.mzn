include "diffn_k.mzn";

%% Parameters
int: n; % no of different products
array[1..4] of int: shelves; % dimensions and number of shelves
array[1..n, 1..4] of int: products; % dimensions and number of products

%% Derived Parameters
int: no_shelves = shelves[4];
array [1..n] of int: no_products = products[..,4];
int: total_products = sum(products[..,4]);
array[1..total_products, 1..3] of int: product_sizes = array2d(1..total_products, 1..3,
        [
            [products[i,1], products[i,2], products[i,3]][x]
            | i in 1..n, _ in 1..products[i,4], x in 1..3
        ]);

%% Descision Variables

% array[1..no_shelves, 1..no_product] of var 0..max(products[..,4]): shelves_content;

% Product i is placed on shelf j
array[1..total_products] of var 1..no_shelves: product_placement::add_to_output;

array[1..total_products, 1..3] of var 1..max(shelves[1..3]): startXYZ::add_to_output;

var 1..no_shelves: no_loaded_shelves;

array[1..no_shelves] of var 1..total_products: no_products_in_shelf::add_to_output;

% array[1..no_prod, 1..3, 1..no_shelves] of var 0..max(shelves[1..3]): product_placement;
%% Constraints

% Make sure all products are placed in a shelf
% constraint forall(i in 1..no_prod) (sum(shelves_content[..,i]) = no_prod[i]);

constraint forall(i in 1..no_shelves) (no_products_in_shelf[i] = count(product_placement, i));

constraint forall(i in 1..no_shelves where no_products_in_shelf[i] > 0)
    (
        diffn_k
        (
            array2d(1..no_products_in_shelf[i], 1..3,
            [[startXYZ[j, 1], startXYZ[j, 2], startXYZ[j, 3]][x]
            | j in 1..total_products, x in 1..3 where product_placement[j, 4] == i]),
            array2d(1..no_products_in_shelf[i], 1..3,
            [[product_sizes[j, 1], product_sizes[j, 2], product_sizes[j, 3]][x]
            | j in 1..total_products, x in 1..3 where product_placement[j] == i])
        )
    );


constraint forall(i in 1..total_products)
    (
        startXYZ[i, 1] + product_sizes[i, 1] <= shelves[1] /\
        startXYZ[i, 1] >= 0
    );
constraint forall(i in 1..total_products)
    (
        startXYZ[i, 2] + product_sizes[i, 2] <= shelves[2] /\
        startXYZ[i, 2] >= 0
    );
constraint forall(i in 1..total_products)
    (
        startXYZ[i, 3] + product_sizes[i, 3] <= shelves[3] /\
        startXYZ[i, 3] >= 0
    );

solve minimize no_loaded_shelves;
