import { DialogProps } from '@mui/material';
export declare type VariantType = 'error' | 'default';
export declare type VdsDialogProps = DialogProps & {
    variant?: VariantType;
};
export declare const VdsDialog: import("@emotion/styled").StyledComponent<DialogProps & import("@mui/system").MUIStyledCommonProps<import("@mui/material").Theme>, {}, {}>;
