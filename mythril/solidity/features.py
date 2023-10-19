TRANSFER_METHODS = ["transfer", "send"]


class SolidityFeatureExtractor:
    def __init__(self, ast):
        self.ast = ast

    def extract_features(self):
        function_features = {}
        function_nodes = self.find_function_nodes(self.ast)
        modifier_vars = {}
        for modifier_node in self.find_modifier_nodes(self.ast):
            modifier_vars[modifier_node["name"]] = self.find_variables_in_require(
                modifier_node
            )
            modifier_vars[modifier_node["name"]].update(
                self.find_variables_in_if(modifier_node)
            )

        for node in function_nodes:
            function_name = self.get_function_name(node)
            contains_selfdestruct = self.contains_selfdestruct(node)
            contains_call = self.contains_call(node)
            contains_delegatecall = self.contains_delegatecall(node)
            contains_callcode = self.contains_callcode(node)
            contains_staticcall = self.contains_staticcall(node)
            all_require_vars = self.find_variables_in_require(node)
            ether_vars = self.extract_address_variable(node)

            for modifier in node.get("modifiers", []):
                all_require_vars.update(modifier_vars[modifier["modifierName"]["name"]])
            is_payable = self.is_function_payable(node)
            has_isowner_modifier = self.has_isowner_modifier(node)
            contains_assert = self.contains_assert(node)
            function_features[function_name] = {
                "contains_selfdestruct": contains_selfdestruct,
                "contains_call": contains_call,
                "is_payable": is_payable,
                "has_owner_modifier": has_isowner_modifier,
                "contains_assert": contains_assert,
                "contains_callcode": contains_callcode,
                "contains_delegatecall": contains_delegatecall,
                "contains_staticcall": contains_staticcall,
                "all_require_vars": all_require_vars,
                "transfer_vars": ether_vars,
            }

        return function_features

    def find_function_nodes(self, node):
        if node["nodeType"] == "FunctionDefinition":
            yield node

        if "nodes" in node:
            for child_node in node["nodes"]:
                yield from self.find_function_nodes(child_node)

    def find_modifier_nodes(self, node):
        if node["nodeType"] == "ModifierDefinition":
            yield node

        if "nodes" in node:
            for child_node in node["nodes"]:
                yield from self.find_modifier_nodes(child_node)

    def get_function_name(self, node):
        return node["name"]

    def contains_command(self, node, command):
        if isinstance(node, dict):
            if command in node.values():
                return True

            for value in node.values():
                if isinstance(value, (dict, list)):
                    if self.contains_command(value, command):
                        return True

        elif isinstance(node, list):
            for item in node:
                if self.contains_command(item, command):
                    return True

        return False

    def contains_call(self, node):
        return self.contains_command(node, "call")

    def is_function_payable(self, node):
        return node.get("stateMutability") == "payable"

    def has_isowner_modifier(self, node):
        if "modifiers" in node:
            for modifier in node["modifiers"]:
                if modifier["modifierName"]["name"].lower() in ("isowner", "onlyowner"):
                    return True
        return False

    def contains_assert(self, node):
        return self.contains_command(node, "assert")

    def contains_selfdestruct(self, node):
        return self.contains_command(node, "selfdestruct")

    def contains_delegatecall(self, node):
        return self.contains_command(node, "delegatecall")

    def contains_callcode(self, node):
        return self.contains_command(node, "callcode")

    def contains_staticcall(self, node):
        return self.contains_command(node, "staticcall")

    def contains_require(self, node):
        return self.contains_command(node, "require")

    def extract_nodes(self, node, command, parent=None):
        node_list = []
        if isinstance(node, dict):
            if command in node.values():
                node_list.append((parent, node))

            for key, value in node.items():
                if isinstance(value, (dict, list)):
                    node_list.extend(self.extract_nodes(value, command, parent=node))
        elif isinstance(node, list):
            for item in node:
                node_list.extend(self.extract_nodes(item, command, parent=node))
        return node_list

    def find_all_variables(self, node):
        variables = set()

        def traverse(node):
            if isinstance(node, dict):
                for key, value in node.items():
                    if key == "nodeType" and value == "Identifier":
                        if "name" in node:
                            variables.add(node["name"])
                    elif isinstance(value, (dict, list)):
                        traverse(value)
            elif isinstance(node, list):
                for item in node:
                    traverse(item)

        traverse(node)
        return variables

    def find_variables_in_require(self, node):

        nodes = self.extract_nodes(node, "require")
        variables = set()
        for parent, _ in nodes:
            if "arguments" in parent:
                arguments = parent["arguments"]
                for argument in arguments:
                    variables.update(self.find_all_variables(argument))
        return variables

    def find_variables_in_if(self, node):
        variables = []

        def traverse(node):
            if "condition" in node:
                condition = node["condition"]
                if (
                    "leftExpression" in condition
                    and condition["leftExpression"]["nodeType"] == "Identifier"
                ):
                    variables.append(condition["leftExpression"]["name"])
                if (
                    "rightExpression" in condition
                    and condition["rightExpression"]["nodeType"] == "Identifier"
                ):
                    variables.append(condition["rightExpression"]["name"])

                traverse(condition)

            if "falseBody" in node and node["falseBody"]:
                traverse(node["falseBody"])

            if "trueBody" in node and node["trueBody"]:
                if (
                    "nodeType" in node["trueBody"]
                    and node["trueBody"]["nodeType"] == "Block"
                ):
                    statements = node["trueBody"].get("statements", [])
                    for statement in statements:
                        traverse(statement)
                else:
                    traverse(node["trueBody"])

            if "body" in node and node["body"]:
                if "nodeType" in node["body"] and node["body"]["nodeType"] == "Block":
                    statements = node["body"].get("statements", [])
                    for statement in statements:
                        traverse(statement)
                else:
                    traverse(node["body"])

        traverse(node)

        return variables

    def extract_address_variable(self, node):
        if node is None or isinstance(node, (int, str)):
            return set([])
        transfer_vars = set([])
        if (
            node.get("nodeType", "") == "ExpressionStatement"
            and node.get("expression", {}).get("nodeType") == "FunctionCall"
        ):
            expression = node["expression"].get("expression", None)
            if expression is not None and (
                expression["nodeType"] == "MemberAccess"
                and expression["memberName"] in TRANSFER_METHODS
            ):
                address_variable = expression["expression"].get("name")
                if address_variable:
                    transfer_vars.update(set([address_variable]))

        for key, value in node.items():
            if isinstance(value, dict):
                transfer_vars.update(self.extract_address_variable(value))

            elif isinstance(value, list):
                for item in value:
                    transfer_vars.update(self.extract_address_variable(item))

        return transfer_vars
