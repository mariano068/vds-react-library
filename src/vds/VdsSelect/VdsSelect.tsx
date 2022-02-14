import { styled } from '@mui/material';
import FormControl from '@mui/material/FormControl';
import Select, { SelectProps as MuiSelectProps } from '@mui/material/Select';
import * as React from 'react';
import { AiFillMinusCircle } from 'react-icons/ai';

export type SelectProps = {
    label?: string,
    helperText?: string,
    errorText?: string,
} & MuiSelectProps;

const StyledTextFieldContainer = styled('div')(() => ({
    display: 'flex',
    minHeight: '96px',
    fontFamily: '-apple-system, BlinkMacSystemFont, "Segoe UI", Roboto, Oxygen-Sans, Ubuntu, Cantarell, "Helvetica Neue", sans-serif',
    flexDirection: 'column',
    width: 'initial',
    input: { padding: '0 !important' },
    '.MuiOutlinedInput-root': {
        borderRadius: 'unset',
        'minHeight': '40px',
    }
}));

const StyledInfosContainer = styled('div')({
    marginBottom: '12px',
    display: 'flex',
    flexDirection: 'column'
});

const StyledErrorContainer = styled('span')({
    fontSize: "12px",
    color: "#D82829",
    lineHeight: "18px",
    fontFamily: "Roboto",
    fontWeight: 400,
    display: 'flex',
    alignItems: 'center',
    textAlign: "left"
});

const StyledLabelContainer = styled('span')(({ disabled, readOnly }: Partial<SelectProps>) => ({
    fontSize: "14px",
    color: readOnly ? "black" : disabled ? "#9DA6AD" : "#152935",
    letterSpacing: "0",
    lineHeight: "18px",
    fontFamily: "Roboto !important",
    fontWeight: 500,
    textAlign: "left",
    borderRadius: 'unset',
    marginBottom: '8px'
}));

const StyledSelect = styled(Select, { shouldForwardProp: (props: any) => props } as any)(({ disabled, readOnly, error, multiple }: any) => ({
    border: disabled ? '1px solid #C1C1C4' : readOnly ? '1px solid #C1C1C4' : error ? '1px solid #D82829' : '1px solid #C9D9E8',
    backgroundColor: (disabled || readOnly) ? '#FAFBFD' : '#F2F5F8',
    font: 'unset',
    borderRadius: 'unset',
    cursor: disabled ? 'not-allowed!important' : 'pointer!important',
    '*': {
        cursor: disabled ? 'not-allowed!important' : 'pointer!important'
    },
    ':hover': {
        border: disabled ? '1px solid #0090D1' : readOnly ? '1px solid #C1C1C4' : error ? '1px solid #D82829' : '1px solid #0090D1!important'
    },
    '::placeholder': {
        fontSize: "14px!important",
        color: (disabled || readOnly) ? "#C1C1C4" : "#9DA6AD",
        lineHeight: "18px",
        fontFamily: "Roboto",
        fontWeight: 400,
        textAlign: "left"
    },
    '::before': {
        all: 'unset'
    },
    '::after': {
        all: 'unset'
    },
    '.MuiSelect-select': {
        padding: multiple ? '6px 14px' : '7.7px 14px'
    },
    '.MuiNativeSelect-select': {
        padding: multiple ? '6px 14px' : '7.7px 14px'
    },
    'input': { display: 'none' },
    'fieldset': { display: 'none' },
}));

export const VdsSelect = (props: SelectProps) => {

    const { label, placeholder, errorText, helperText, children, fullWidth, ...MuiSelectProps } = props;

    return (
        <StyledTextFieldContainer>
            {label && <StyledInfosContainer>
                <StyledLabelContainer>
                    {label}
                </StyledLabelContainer>
            </StyledInfosContainer>}
            <FormControl sx={{ minWidth: 250 }} size="small">
                <StyledSelect {...MuiSelectProps}>
                    {children}
                </StyledSelect>
            </FormControl>
            {props.error && (
                <StyledErrorContainer>
                    <AiFillMinusCircle style={{ fill: '#D82829', fontSize: '13px', padding: '0 5px' }} /> {props.errorText}
                </StyledErrorContainer>
            )}
        </StyledTextFieldContainer>
    );
}
