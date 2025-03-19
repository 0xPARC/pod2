import { SerializedValue } from "./pod-serialization";

export enum ValueType {
  String = "String",
  Int = "Int",
  Bool = "Bool",
  Array = "Array",
  Set = "Set",
  Dictionary = "Dictionary",
  Raw = "Raw"
}

export type PrimitiveValue = string | number | boolean;
export type ArrayValue = SerializedValue[];
export type SetValue = Set<SerializedValue>;
export type DictionaryValue = Record<string, SerializedValue>;
export type PodValue = PrimitiveValue | ArrayValue | SetValue | DictionaryValue;

export interface TreeNode {
  id: string;
  key: string;
  type: ValueType;
  value:
    | string
    | boolean
    | Record<string, SerializedValue>
    | SerializedValue[]
    | Set<SerializedValue>;
  children?: TreeNode[];
}
