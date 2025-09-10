use {
    proc_macro::TokenStream,
    quote::{format_ident, quote},
    syn::{
        parse_macro_input,
        Attribute, Data, DataStruct, DeriveInput, Field, Fields, Meta, Type, Token,
        spanned::Spanned,
    },
};

#[proc_macro_derive(Contextual, attributes(scheme))]
pub fn derive_contextual(item: TokenStream) -> TokenStream {
    let input = parse_macro_input!(item as DeriveInput);
    let DeriveInput { attrs, vis, ident, generics, data } = input;
    let scheme = {
        let mut scheme_opt = None;
        for attr in attrs.iter() {
            let Attribute { meta, .. } = attr;
            let Some(path_ident) = meta.path().get_ident() else {
                continue;
            };
            if path_ident != "scheme" {
                continue;
            }
            let Meta::List(meta_list) = meta else {
                panic!("invalid #[scheme(...)] attribute");
            };
            let scheme: Type = {
                meta_list
                .parse_args()
                .expect("expected a Type")
            };
            match scheme_opt {
                None => scheme_opt = Some(scheme),
                Some(_) => {
                    panic!("duplicate #[scheme(...)] attribute");
                },
            }
        }
        scheme_opt.expect("missing #[scheme(...)] attribute")
    };
    let ident_raw = format_ident!("Raw{}", ident);
    let output = match data {
        Data::Struct(data_struct) => {
            derive_contextual_struct(scheme, vis, ident, ident_raw, generics, data_struct)
        },
        Data::Enum(data_enum) => {
            derive_contextual_enum(scheme, vis, ident, ident_raw, generics, data_enum)
        },
        _ => panic!("derive(Contextual) can only be applied to structs and enums"),
    };

    output.into()
}

fn derive_contextual_struct(
    scheme: Type,
    vis: syn::Visibility,
    ident: syn::Ident,
    ident_raw: syn::Ident,
    generics: syn::Generics,
    data_struct: syn::DataStruct,
) -> proc_macro2::TokenStream {
    let DataStruct { struct_token, fields, semi_token } = data_struct;

    match fields {
        Fields::Named(fields) => {
            derive_contextual_struct_named(
                scheme, vis, ident, ident_raw, generics, struct_token, fields,
            )
        },
        Fields::Unnamed(fields) => {
            derive_contextual_struct_unnamed(
                scheme, vis, ident, ident_raw, generics, struct_token, fields, semi_token.unwrap(),
            )
        },
        Fields::Unit => {
            panic!("derive(Contextual) cannot be applied to unit structs");
        },
    }
}

fn derive_contextual_struct_named(
    scheme: Type,
    vis: syn::Visibility,
    ident: syn::Ident,
    ident_raw: syn::Ident,
    generics: syn::Generics,
    struct_token: Token![struct],
    fields: syn::FieldsNamed,
) -> proc_macro2::TokenStream {
    let field_names: Vec<_> = {
        fields
        .named
        .iter()
        .map(|field| field.ident.as_ref().unwrap())
        .collect()
    };
    let fields_raw: Vec<_> = {
        fields
        .named
        .iter()
        .map(|field| {
            let Field { attrs, vis, mutability: _, ident, colon_token, ty } = field;
            let ident = ident.as_ref().unwrap();
            let colon_token = colon_token.unwrap();
            quote! {
                #(#attrs)* #vis #ident #colon_token ::core_tt::Weaken<<#ty as ::core_tt::Contextual<#scheme>>::Raw>,
            }
        })
        .collect()
    };
    let field_tys: Vec<_> = {
        fields
        .named
        .iter()
        .map(|field| &field.ty)
        .collect()
    };
    let (impl_generics, type_generics, where_clause) = generics.split_for_impl();

    quote! {
        #[doc(hidden)]
        #vis #struct_token #ident_raw #generics {
            #(#fields_raw)*
        }

        impl #impl_generics ::core::fmt::Debug for #ident_raw #type_generics
        where
            #(#field_tys: ::core::fmt::Debug,)*
        {
            fn fmt(&self, f: &mut ::core::fmt::Formatter) -> ::core::fmt::Result {
                let #ident_raw { #(#field_names,)* } = self;
                let mut debug = f.debug_struct(stringify!(#ident_raw));
                #(
                    debug.field(stringify!(#field_names), #field_names);
                )*
                debug.finish()
            }
        }

        impl #impl_generics ::core::cmp::PartialEq for #ident_raw #type_generics
        where
            #(#field_tys: ::core::cmp::PartialEq,)*
        {
            fn eq(&self, other: &#ident_raw #type_generics) -> bool {
                true #(&& {
                    let #ident_raw { #field_names: lhs, .. } = self;
                    let #ident_raw { #field_names: rhs, .. } = other;
                    ::core::cmp::PartialEq::eq(lhs, rhs)
                })*
            }
        }

        impl #impl_generics ::core::clone::Clone for #ident_raw #type_generics
        where
            #(#field_tys: ::core::clone::Clone,)*
        {
            fn clone(&self) -> #ident_raw #type_generics {
                let #ident_raw { #(#field_names,)* } = self;
                #ident_raw {
                    #(#field_names: #field_names.clone(),)*
                }
            }
        }

        impl #impl_generics ::core_tt::Substitute<#scheme> for #ident_raw #type_generics
        #where_clause
        {
            type RawSubstOutput = #ident_raw #type_generics;

            fn to_subst_output(&self, _num_usages: usize) -> #ident_raw #type_generics {
                self.clone()
            }

            fn subst(
                &self,
                filter: &::core_tt::Usages,
                var_term: ::core_tt::RawTm<#scheme>,
            ) -> ::core_tt::Weaken<#ident_raw #type_generics> {
                let #ident_raw { #(#field_names,)* } = self;

                #(
                    let mut #field_names = #field_names.subst(filter, &var_term);
                )*

                let usages = ::core_tt::Usages::merge_mut([#(&mut #field_names.usages,)*]);
                let weak = #ident_raw { #(#field_names,)* };
                ::core_tt::Weaken { usages, weak }
            }

            fn eliminates_var(&self, index: usize) -> bool {
                let #ident_raw { #(#field_names,)* } = self;
                false #(|| #field_names.eliminates_var(index))*
            }
        }

        impl #impl_generics ::core_tt::Contextual<#scheme> for #ident #type_generics
        #where_clause
        {
            type Raw = #ident_raw #type_generics;

            fn ctx(&self) -> ::core_tt::Ctx<#scheme> {
                let #ident { #(#field_names,)* } = self;
                let ctx_opt = None;

                #(
                    let next_ctx = ::core_tt::Contextual::ctx(#field_names);
                    let ctx_opt = match ctx_opt {
                        None => Some(next_ctx),
                        Some(ctx) => {
                            assert_eq!(ctx, next_ctx);
                            Some(ctx)
                        },
                    };
                )*

                ctx_opt.unwrap()
            }

            fn into_raw(self) -> (
                ::core_tt::Ctx<#scheme>,
                ::core_tt::Weaken<#ident_raw #type_generics>,
            ) {
                let #ident { #(#field_names,)* } = self;
                let ctx_opt = None;

                #(
                    let (next_ctx, mut #field_names) = ::core_tt::Contextual::into_raw(#field_names);
                    let ctx_opt = match ctx_opt {
                        None => Some(next_ctx),
                        Some(ctx) => {
                            assert_eq!(ctx, next_ctx);
                            Some(ctx)
                        },
                    };
                )*

                let ctx = ctx_opt.unwrap();
                let usages = ::core_tt::Usages::merge_mut([#(&mut #field_names.usages,)*]);
                let weak = #ident_raw { #(#field_names,)* };
                let raw = ::core_tt::Weaken { usages, weak };
                (ctx, raw)
            }

            fn from_raw(
                ctx: ::core_tt::Ctx<#scheme>,
                raw: ::core_tt::Weaken<#ident_raw #type_generics>,
            ) -> #ident #type_generics {
                let ::core_tt::Weaken { usages, weak } = raw;
                let #ident_raw { #(#field_names,)* } = weak;

                #(
                    let #field_names = ::core_tt::Contextual::from_raw(ctx.clone(), #field_names.unfilter(&usages));
                )*

                #ident { #(#field_names,)* }
            }

            fn eliminates_var(&self, index: usize) -> bool {
                let #ident { #(#field_names,)* } = self;
                false #(|| #field_names.eliminates_var(index))*
            }
        }
    }
}

fn derive_contextual_struct_unnamed(
    scheme: Type,
    vis: syn::Visibility,
    ident: syn::Ident,
    ident_raw: syn::Ident,
    generics: syn::Generics,
    struct_token: Token![struct],
    fields: syn::FieldsUnnamed,
    semi_token: Token![;],
) -> proc_macro2::TokenStream {
    let field_names: Vec<_> = {
        (0..fields.unnamed.len())
        .map(|index| format_ident!("field_{}", index))
        .collect()
    };
    let fields_raw: Vec<_> = {
        fields
        .unnamed
        .iter()
        .map(|field| {
            let Field { attrs, vis, mutability: _, ident: _, colon_token: _, ty } = field;
            quote! {
                #(#attrs)* #vis ::core_tt::Weaken<<#ty as ::core_tt::Contextual<#scheme>>::Raw>,
            }
        })
        .collect()
    };
    let field_indices: Vec<_> = {
        fields
        .unnamed
        .iter()
        .enumerate()
        .map(|(index, field)| {
            syn::Index {
                index: index as u32,
                span: field.span(),
            }
        })
        .collect()
    };
    let field_tys: Vec<_> = {
        fields
        .unnamed
        .iter()
        .map(|field| &field.ty)
        .collect()
    };
    let (impl_generics, type_generics, where_clause) = generics.split_for_impl();

    quote! {
        #[doc(hidden)]
        #vis #struct_token #ident_raw #generics (
            #(#fields_raw)*
        ) #semi_token

        impl #impl_generics ::core::fmt::Debug for #ident_raw #type_generics
        where
            #(#field_tys: ::core::fmt::Debug,)*
        {
            fn fmt(&self, f: &mut ::core::fmt::Formatter) -> ::core::fmt::Result {
                let #ident_raw(#(#field_names,)*) = self;
                let mut debug = f.debug_tuple(stringify!(#ident_raw));
                #(
                    debug.field(#field_names);
                )*
                debug.finish()
            }
        }

        impl #impl_generics ::core::cmp::PartialEq for #ident_raw #type_generics
        where
            #(#field_tys: ::core::cmp::PartialEq,)*
        {
            fn eq(&self, other: &#ident_raw #type_generics) -> bool {
                true #(
                    && ::core::cmp::PartialEq::eq(&self.#field_indices, &other.#field_indices)
                )*
            }
        }

        impl #impl_generics ::core::clone::Clone for #ident_raw #type_generics
        where
            #(#field_tys: ::core::clone::Clone,)*
        {
            fn clone(&self) -> #ident_raw #type_generics {
                let #ident_raw(#(#field_names,)*) = self;
                #ident_raw(
                    #(#field_names.clone(),)*
                )
            }
        }

        impl #impl_generics ::core_tt::Substitute<#scheme> for #ident_raw #type_generics
        #where_clause
        {
            type RawSubstOutput = #ident_raw #type_generics;

            fn to_subst_output(&self, _num_usages: usize) -> #ident_raw #type_generics {
                self.clone()
            }

            fn subst(
                &self,
                filter: &::core_tt::Usages,
                var_term: ::core_tt::RawTm<#scheme>,
            ) -> ::core_tt::Weaken<#ident_raw #type_generics> {
                let #ident_raw ( #(#field_names,)* ) = self;

                #(
                    let mut #field_names = #field_names.subst(filter, &var_term);
                )*

                let usages = ::core_tt::Usages::merge_mut([#(&mut #field_names.usages,)*]);
                let weak = #ident_raw ( #(#field_names,)* );
                ::core_tt::Weaken { usages, weak }
            }

            fn eliminates_var(&self, index: usize) -> bool {
                let #ident_raw ( #(#field_names,)* ) = self;
                false #(|| #field_names.eliminates_var(index))*
            }
        }

        impl #impl_generics ::core_tt::Contextual<#scheme> for #ident #type_generics
        #where_clause
        {
            type Raw = #ident_raw #type_generics;

            fn ctx(&self) -> ::core_tt::Ctx<#scheme> {
                let #ident ( #(#field_names,)* ) = self;
                let ctx_opt = None;

                #(
                    let next_ctx = ::core_tt::Contextual::ctx(#field_names);
                    let ctx_opt = match ctx_opt {
                        None => Some(next_ctx),
                        Some(ctx) => {
                            assert_eq!(ctx, next_ctx);
                            Some(ctx)
                        },
                    };
                )*

                ctx_opt.unwrap()
            }

            fn into_raw(self) -> (
                ::core_tt::Ctx<#scheme>,
                ::core_tt::Weaken<#ident_raw #type_generics>,
            ) {
                let #ident ( #(#field_names,)* ) = self;
                let ctx_opt = None;

                #(
                    let (next_ctx, mut #field_names) = ::core_tt::Contextual::into_raw(#field_names);
                    let ctx_opt = match ctx_opt {
                        None => Some(next_ctx),
                        Some(ctx) => {
                            assert_eq!(ctx, next_ctx);
                            Some(ctx)
                        },
                    };
                )*

                let ctx = ctx_opt.unwrap();
                let usages = ::core_tt::Usages::merge_mut([#(&mut #field_names.usages,)*]);
                let weak = #ident_raw ( #(#field_names,)* );
                let raw = ::core_tt::Weaken { usages, weak };
                (ctx, raw)
            }

            fn from_raw(
                ctx: ::core_tt::Ctx<#scheme>,
                raw: ::core_tt::Weaken<#ident_raw #type_generics>,
            ) -> #ident #type_generics {
                let ::core_tt::Weaken { usages, weak } = raw;
                let #ident_raw ( #(#field_names,)* ) = weak;

                #(
                    let #field_names = ::core_tt::Contextual::from_raw(ctx.clone(), #field_names.unfilter(&usages));
                )*

                #ident ( #(#field_names,)* )
            }

            fn eliminates_var(&self, index: usize) -> bool {
                let #ident ( #(#field_names,)* ) = self;
                false #(|| #field_names.eliminates_var(index))*
            }
        }
    }
}

fn derive_contextual_enum(
    scheme: Type,
    vis: syn::Visibility,
    ident: syn::Ident,
    ident_raw: syn::Ident,
    generics: syn::Generics,
    data_enum: syn::DataEnum,
) -> proc_macro2::TokenStream {
    let syn::DataEnum { enum_token, brace_token: _, variants } = data_enum;

    let variants_raw: Vec<_> = {
        variants
        .iter()
        .map(|variant| {
            let syn::Variant { attrs, ident, fields, discriminant } = variant;
            let discriminant = match discriminant.as_ref() {
                Some((eq_token, expr)) => quote! { #eq_token #expr },
                None => quote! {},
            };
            match fields {
                Fields::Named(fields) => {
                    let fields_raw: Vec<_> = {
                        fields
                        .named
                        .iter()
                        .map(|field| {
                            let Field { attrs, vis: _, mutability: _, ident, colon_token, ty } = field;
                            let ident = ident.as_ref().unwrap();
                            let colon_token = colon_token.unwrap();
                            quote! {
                                #(#attrs)* #ident #colon_token ::core_tt::Weaken<<#ty as ::core_tt::Contextual<#scheme>>::Raw>,
                            }
                        })
                        .collect()
                    };
                    quote! {
                        #(#attrs)* #ident { #(#fields_raw)* } #discriminant,
                    }
                },
                Fields::Unnamed(fields) => {
                    let fields_raw: Vec<_> = {
                        fields
                        .unnamed
                        .iter()
                        .map(|field| {
                            let Field { attrs, vis: _, mutability: _, ident: _, colon_token: _, ty } = field;
                            quote! {
                                #(#attrs)* ::core_tt::Weaken<<#ty as ::core_tt::Contextual<#scheme>>::Raw>,
                            }
                        })
                        .collect()
                    };
                    quote! {
                        #(#attrs)* #ident ( #(#fields_raw)* ) #discriminant,
                    }
                },
                Fields::Unit => {
                    panic!("#[derive(Contextual)] cannot be used on enums with unit variants");
                },
            }
        })
        .collect()
    };

    let field_tys: Vec<_> = {
        variants
        .iter()
        .map(|variant| {
            let syn::Variant { attrs: _, ident: _, fields, discriminant: _ } = variant;
            match fields {
                Fields::Named(fields) => {
                    fields
                    .named
                    .iter()
                    .map(|field| &field.ty)
                    .collect::<Vec<_>>()
                    .into_iter()
                },
                Fields::Unnamed(fields) => {
                    fields
                    .unnamed
                    .iter()
                    .map(|field| &field.ty)
                    .collect::<Vec<_>>()
                    .into_iter()
                },
                Fields::Unit => unreachable!(),
            }
        })
        .flatten()
        .collect()
    };

    let debug_branches = {
        variants
        .iter()
        .map(|variant| {
            let syn::Variant { attrs: _, ident: variant_ident, fields, discriminant: _ } = variant;
            match fields {
                Fields::Named(fields) => {
                    let field_names: Vec<_> = {
                        fields
                        .named
                        .iter()
                        .map(|field| field.ident.as_ref().unwrap())
                        .collect()
                    };
                    quote! {
                        #ident_raw::#variant_ident { #(#field_names,)* } => {
                            let mut debug = f.debug_struct(stringify!(#variant_ident));
                            #(
                                debug.field(stringify!(#field_names), #field_names);
                            )*
                            debug.finish()
                        },
                    }
                },
                Fields::Unnamed(fields) => {
                    let field_names: Vec<_> = {
                        (0..fields.unnamed.len())
                        .map(|index| format_ident!("field_{}", index))
                        .collect()
                    };
                    quote! {
                        #ident_raw::#variant_ident(#(#field_names,)*) => {
                            let mut debug = f.debug_tuple(stringify!(#variant_ident));
                            #(
                                debug.field(#field_names);
                            )*
                            debug.finish()
                        },
                    }
                },
                Fields::Unit => unreachable!(),
            }
        })
    };

    let eq_branches = {
        variants
        .iter()
        .map(|variant| {
            let syn::Variant { attrs: _, ident: variant_ident, fields, discriminant: _ } = variant;
            match fields {
                Fields::Named(fields) => {
                    let field_names: Vec<_> = {
                        fields
                        .named
                        .iter()
                        .map(|field| field.ident.as_ref().unwrap())
                        .collect()
                    };
                    let field_names_lhs: Vec<_> = {
                        field_names
                        .iter()
                        .map(|name| format_ident!("{}_lhs", name))
                        .collect()
                    };
                    let field_names_rhs: Vec<_> = {
                        field_names
                        .iter()
                        .map(|name| format_ident!("{}_rhs", name))
                        .collect()
                    };
                    quote! {
                        (
                            #ident_raw::#variant_ident { #(#field_names: #field_names_lhs,)* },
                            #ident_raw::#variant_ident { #(#field_names: #field_names_rhs,)* },
                        ) => {
                            true #(&&
                                ::core::cmp::PartialEq::eq(#field_names_lhs, #field_names_rhs)
                            )*
                        },
                    }
                },
                Fields::Unnamed(fields) => {
                    let field_names: Vec<_> = {
                        (0..fields.unnamed.len())
                        .map(|index| format_ident!("field_{}", index))
                        .collect()
                    };
                    let field_names_lhs: Vec<_> = {
                        field_names
                        .iter()
                        .map(|name| format_ident!("{}_lhs", name))
                        .collect()
                    };
                    let field_names_rhs: Vec<_> = {
                        field_names
                        .iter()
                        .map(|name| format_ident!("{}_rhs", name))
                        .collect()
                    };
                    quote! {
                        (
                            #ident_raw::#variant_ident(#(#field_names_lhs,)*),
                            #ident_raw::#variant_ident(#(#field_names_rhs,)*),
                        ) => {
                            true #(&&
                                ::core::cmp::PartialEq::eq(#field_names_lhs, #field_names_rhs)
                            )*
                        },
                    }
                },
                Fields::Unit => unreachable!(),
            }
        })
    };

    let clone_branches = {
        variants
        .iter()
        .map(|variant| {
            let syn::Variant { attrs: _, ident: variant_ident, fields, discriminant: _ } = variant;
            match fields {
                Fields::Named(fields) => {
                    let field_names: Vec<_> = {
                        fields
                        .named
                        .iter()
                        .map(|field| field.ident.as_ref().unwrap())
                        .collect()
                    };
                    quote! {
                        #ident_raw::#variant_ident { #(#field_names,)* } => {
                            #ident_raw::#variant_ident {
                                #(#field_names: #field_names.clone(),)*
                            }
                        },
                    }
                },
                Fields::Unnamed(fields) => {
                    let field_names: Vec<_> = {
                        (0..fields.unnamed.len())
                        .map(|index| format_ident!("field_{}", index))
                        .collect()
                    };
                    quote! {
                        #ident_raw::#variant_ident(#(#field_names,)*) => {
                            #ident_raw::#variant_ident(
                                #(#field_names.clone(),)*
                            )
                        },
                    }
                },
                Fields::Unit => unreachable!(),
            }
        })
    };

    let ctx_branches = {
        variants
        .iter()
        .map(|variant| {
            let syn::Variant { attrs: _, ident: variant_ident, fields, discriminant: _ } = variant;
            match fields {
                Fields::Named(fields) => {
                    let field_names: Vec<_> = {
                        fields
                        .named
                        .iter()
                        .map(|field| field.ident.as_ref().unwrap())
                        .collect()
                    };
                    quote! {
                        #ident::#variant_ident { #(#field_names,)* } => {
                            let ctx_opt = None;
                            #(
                                let next_ctx = ::core_tt::Contextual::ctx(#field_names);
                                let ctx_opt = match ctx_opt {
                                    None => Some(next_ctx),
                                    Some(ctx) => {
                                        assert_eq!(ctx, next_ctx);
                                        Some(ctx)
                                    },
                                };
                            )*
                            ctx_opt.unwrap()
                        },
                    }
                },
                Fields::Unnamed(fields) => {
                    let field_names: Vec<_> = {
                        (0..fields.unnamed.len())
                        .map(|index| format_ident!("field_{}", index))
                        .collect()
                    };
                    quote! {
                        #ident::#variant_ident(#(#field_names,)*) => {
                            let ctx_opt = None;
                            #(
                                let next_ctx = ::core_tt::Contextual::ctx(#field_names);
                                let ctx_opt = match ctx_opt {
                                    None => Some(next_ctx),
                                    Some(ctx) => {
                                        assert_eq!(ctx, next_ctx);
                                        Some(ctx)
                                    },
                                };
                            )*
                            ctx_opt.unwrap()
                        },
                    }
                },
                Fields::Unit => unreachable!(),
            }
        })
    };

    let subst_branches = {
        variants
        .iter()
        .map(|variant| {
            let syn::Variant { attrs: _, ident: variant_ident, fields, discriminant: _ } = variant;
            match fields {
                Fields::Named(fields) => {
                    let field_names: Vec<_> = {
                        fields
                        .named
                        .iter()
                        .map(|field| field.ident.as_ref().unwrap())
                        .collect()
                    };
                    quote! {
                        #ident_raw::#variant_ident { #(#field_names,)* } => {
                            #(
                                let mut #field_names = #field_names.subst(filter, &var_term);
                            )*

                            let usages = ::core_tt::Usages::merge_mut([#(&mut #field_names.usages,)*]);
                            let weak = #ident_raw::#variant_ident { #(#field_names,)* };
                            ::core_tt::Weaken { usages, weak }
                        },
                    }
                },
                Fields::Unnamed(fields) => {
                    let field_names: Vec<_> = {
                        (0..fields.unnamed.len())
                        .map(|index| format_ident!("field_{}", index))
                        .collect()
                    };
                    quote! {
                        #ident_raw::#variant_ident(#(#field_names,)*) => {
                            #(
                                let mut #field_names = #field_names.subst(filter, &var_term);
                            )*

                            let usages = ::core_tt::Usages::merge_mut([#(&mut #field_names.usages,)*]);
                            let weak = #ident_raw::#variant_ident(#(#field_names,)*);
                            ::core_tt::Weaken { usages, weak }
                        },
                    }
                },
                Fields::Unit => unreachable!(),
            }
        })
    };

    let raw_eliminates_var_branches = {
        variants
        .iter()
        .map(|variant| {
            let syn::Variant { attrs: _, ident: variant_ident, fields, discriminant: _ } = variant;
            match fields {
                Fields::Named(fields) => {
                    let field_names: Vec<_> = {
                        fields
                        .named
                        .iter()
                        .map(|field| field.ident.as_ref().unwrap())
                        .collect()
                    };
                    quote! {
                        #ident_raw::#variant_ident { #(#field_names,)* } => {
                            false #(|| #field_names.eliminates_var(index))*
                        },
                    }
                },
                Fields::Unnamed(fields) => {
                    let field_names: Vec<_> = {
                        (0..fields.unnamed.len())
                        .map(|index| format_ident!("field_{}", index))
                        .collect()
                    };
                    quote! {
                        #ident_raw::#variant_ident(#(#field_names,)*) => {
                            false #(|| #field_names.eliminates_var(index))*
                        },
                    }
                },
                Fields::Unit => unreachable!(),
            }
        })
    };

    let into_raw_branches = {
        variants
        .iter()
        .map(|variant| {
            let syn::Variant { attrs: _, ident: variant_ident, fields, discriminant: _ } = variant;
            match fields {
                Fields::Named(fields) => {
                    let field_names: Vec<_> = {
                        fields
                        .named
                        .iter()
                        .map(|field| field.ident.as_ref().unwrap())
                        .collect()
                    };
                    quote! {
                        #ident::#variant_ident { #(#field_names,)* } => {
                            let ctx_opt = None;

                            #(
                                let (next_ctx, mut #field_names) = ::core_tt::Contextual::into_raw(#field_names);
                                let ctx_opt = match ctx_opt {
                                    None => Some(next_ctx),
                                    Some(ctx) => {
                                        assert_eq!(ctx, next_ctx);
                                        Some(ctx)
                                    },
                                };
                            )*

                            let ctx = ctx_opt.unwrap();
                            let usages = ::core_tt::Usages::merge_mut([#(&mut #field_names.usages,)*]);
                            let weak = #ident_raw::#variant_ident { #(#field_names,)* };
                            let raw = ::core_tt::Weaken { usages, weak };
                            (ctx, raw)
                        },
                    }
                },
                Fields::Unnamed(fields) => {
                    let field_names: Vec<_> = {
                        (0..fields.unnamed.len())
                        .map(|index| format_ident!("field_{}", index))
                        .collect()
                    };
                    quote! {
                        #ident::#variant_ident(#(#field_names,)*) => {
                            let ctx_opt = None;

                            #(
                                let (next_ctx, mut #field_names) = ::core_tt::Contextual::into_raw(#field_names);
                                let ctx_opt = match ctx_opt {
                                    None => Some(next_ctx),
                                    Some(ctx) => {
                                        assert_eq!(ctx, next_ctx);
                                        Some(ctx)
                                    },
                                };
                            )*

                            let ctx = ctx_opt.unwrap();
                            let usages = ::core_tt::Usages::merge_mut([#(&mut #field_names.usages,)*]);
                            let weak = #ident_raw::#variant_ident(#(#field_names,)*);
                            let raw = ::core_tt::Weaken { usages, weak };
                            (ctx, raw)
                        },
                    }
                },
                Fields::Unit => unreachable!(),
            }
        })
    };

    let from_raw_branches = {
        variants
        .iter()
        .map(|variant| {
            let syn::Variant { attrs: _, ident: variant_ident, fields, discriminant: _ } = variant;
            match fields {
                Fields::Named(fields) => {
                    let field_names: Vec<_> = {
                        fields
                        .named
                        .iter()
                        .map(|field| field.ident.as_ref().unwrap())
                        .collect()
                    };
                    quote! {
                        #ident_raw::#variant_ident { #(#field_names,)* } => {
                            #(
                                let #field_names = ::core_tt::Contextual::from_raw(ctx.clone(), #field_names.unfilter(&usages));
                            )*

                            #ident::#variant_ident { #(#field_names,)* }
                        },
                    }
                },
                Fields::Unnamed(fields) => {
                    let field_names: Vec<_> = {
                        (0..fields.unnamed.len())
                        .map(|index| format_ident!("field_{}", index))
                        .collect()
                    };
                    quote! {
                        #ident_raw::#variant_ident(#(#field_names,)*) => {
                            #(
                                let #field_names = ::core_tt::Contextual::from_raw(ctx.clone(), #field_names.unfilter(&usages));
                            )*

                            #ident::#variant_ident(#(#field_names,)*)
                        },
                    }
                },
                Fields::Unit => unreachable!(),
            }
        })
    };

    let eliminates_var_branches = {
        variants
        .iter()
        .map(|variant| {
            let syn::Variant { attrs: _, ident: variant_ident, fields, discriminant: _ } = variant;
            match fields {
                Fields::Named(fields) => {
                    let field_names: Vec<_> = {
                        fields
                        .named
                        .iter()
                        .map(|field| field.ident.as_ref().unwrap())
                        .collect()
                    };
                    quote! {
                        #ident::#variant_ident { #(#field_names,)* } => {
                            false #(|| #field_names.eliminates_var(index))*
                        },
                    }
                },
                Fields::Unnamed(fields) => {
                    let field_names: Vec<_> = {
                        (0..fields.unnamed.len())
                        .map(|index| format_ident!("field_{}", index))
                        .collect()
                    };
                    quote! {
                        #ident::#variant_ident(#(#field_names,)*) => {
                            false #(|| #field_names.eliminates_var(index))*
                        },
                    }
                },
                Fields::Unit => unreachable!(),
            }
        })
    };


    let (impl_generics, type_generics, where_clause) = generics.split_for_impl();

    quote! {
        #vis #enum_token #ident_raw #generics {
            #(#variants_raw)*
        }

        impl #impl_generics ::core::fmt::Debug for #ident_raw #type_generics
        where
            #(#field_tys: ::core::fmt::Debug,)*
        {
            fn fmt(&self, f: &mut ::core::fmt::Formatter) -> ::core::fmt::Result {
                match self {
                    #(#debug_branches)*
                }
            }
        }

        impl #impl_generics ::core::cmp::PartialEq for #ident_raw #type_generics
        where
            #(#field_tys: ::core::cmp::PartialEq,)*
        {
            fn eq(&self, other: &#ident_raw #type_generics) -> bool {
                match (self, other) {
                    #(#eq_branches)*
                    _ => false,
                }
            }
        }

        impl #impl_generics ::core::clone::Clone for #ident_raw #type_generics
        where
            #(#field_tys: ::core::clone::Clone,)*
        {
            fn clone(&self) -> #ident_raw #type_generics {
                match self {
                    #(#clone_branches)*
                }
            }
        }

        impl #impl_generics ::core_tt::Substitute<#scheme> for #ident_raw #type_generics
        #where_clause
        {
            type RawSubstOutput = #ident_raw #type_generics;

            fn to_subst_output(&self, _num_usages: usize) -> #ident_raw #type_generics {
                self.clone()
            }

            fn subst(
                &self,
                filter: &::core_tt::Usages,
                var_term: ::core_tt::RawTm<#scheme>,
            ) -> ::core_tt::Weaken<#ident_raw #type_generics> {
                match self {
                    #(#subst_branches)*
                }
            }

            fn eliminates_var(&self, index: usize) -> bool {
                match self {
                    #(#raw_eliminates_var_branches)*
                }
            }
        }

        impl #impl_generics ::core_tt::Contextual<#scheme> for #ident #type_generics
        #where_clause
        {
            type Raw = #ident_raw #type_generics;

            fn ctx(&self) -> ::core_tt::Ctx<#scheme> {
                match self {
                    #(#ctx_branches)*
                }
            }

            fn into_raw(self) -> (
                ::core_tt::Ctx<#scheme>,
                ::core_tt::Weaken<#ident_raw #type_generics>,
            ) {
                match self {
                    #(#into_raw_branches)*
                }
            }

            fn from_raw(
                ctx: ::core_tt::Ctx<#scheme>,
                raw: ::core_tt::Weaken<#ident_raw #type_generics>,
            ) -> #ident #type_generics {
                let ::core_tt::Weaken { usages, weak } = raw;
                match weak {
                    #(#from_raw_branches)*
                }
            }

            fn eliminates_var(&self, index: usize) -> bool {
                match self {
                    #(#eliminates_var_branches)*
                }
            }
        }
    }
}

