use std::sync::Arc;

use crate::{
    prelude::*,
    type_::{PropertySetter, PropertySetterType},
};

#[derive(Debug, PartialEq, Clone)]
pub(crate) enum AttributeKind {
    AnnotatedAttribute,
    Attribute,
    ClassVar,
    Final,
    Property {
        setter_type: Option<Arc<PropertySetter>>,
        is_final: bool,
        is_abstract: bool,
    },
    Classmethod {
        is_final: bool,
    },
    Staticmethod {
        is_final: bool,
    },
    DefMethod {
        is_final: bool,
    },
}

impl AttributeKind {
    pub fn is_read_only_property(&self) -> bool {
        matches!(
            self,
            Self::Property {
                setter_type: None,
                ..
            }
        )
    }

    pub fn classmethod_or_staticmethod(&self) -> bool {
        matches!(self, Self::Classmethod { .. } | Self::Staticmethod { .. })
    }

    pub fn classvar_like(&self) -> bool {
        matches!(
            self,
            Self::ClassVar
                | Self::DefMethod { .. }
                | Self::Property { .. }
                | Self::Classmethod { .. }
                | Self::Staticmethod { .. }
        )
    }

    pub fn is_final(&self) -> bool {
        matches!(
            self,
            Self::Final
                | Self::DefMethod { is_final: true, .. }
                | Self::Property { is_final: true, .. }
                | Self::Classmethod { is_final: true, .. }
                | Self::Staticmethod { is_final: true, .. }
        )
    }

    pub(crate) fn is_writable(&self) -> bool {
        matches!(
            self,
            Self::Attribute
                | Self::AnnotatedAttribute
                | Self::ClassVar
                | Self::Property {
                    setter_type: Some(_),
                    ..
                }
        )
    }

    pub(crate) fn is_overwritable(&self) -> bool {
        matches!(
            self,
            Self::Attribute
                | Self::AnnotatedAttribute
                | Self::ClassVar
                | Self::Property {
                    is_abstract: false,
                    ..
                }
                | Self::Property {
                    is_abstract: true,
                    setter_type: Some(_),
                    ..
                }
        )
    }

    pub(crate) fn property_setter_type(&self) -> Option<&Type> {
        if let Self::Property { setter_type, .. } = self {
            match &setter_type.as_ref()?.type_ {
                PropertySetterType::OtherType(t) => Some(t),
                PropertySetterType::SameTypeFromCachedProperty => None,
            }
        } else {
            None
        }
    }

    pub fn is_attribute(&self) -> bool {
        matches!(
            self,
            Self::AnnotatedAttribute | Self::Attribute | Self::ClassVar | Self::Final
        )
    }

    pub fn is_cached_property(&self) -> bool {
        if let Self::Property { setter_type, .. } = self {
            matches!(
                setter_type.as_ref().map(|s| &s.type_),
                Some(PropertySetterType::SameTypeFromCachedProperty)
            )
        } else {
            false
        }
    }
}
