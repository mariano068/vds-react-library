import { Grid, MenuItem } from '@mui/material';
import * as React from 'react';
import { VdsSelect } from '../../vds/VdsSelect/VdsSelect';
import { convert } from '../utils';

//#region standard example
export const singleSelection_example_snippet = convert(`
import React from 'react';
import { VdsTextField } from 'vds-components';

export default () => {

    const [state, setState] = React.useState<{ [P in string]: unknown }>({});

    const handleChange = (key: string, value: unknown) => { setState({ ...state, [key]: value }); }

    return (
      <VdsSelect
          disabled={false}
          readOnly={false}
          label='Select text label*'
          MenuProps={{
            PaperProps: {
              style: {
                maxHeight: 224,
                width: 250,
              },
            }
          }}
          onChange={(ev) => handleChange('name', ev.target.value)}
          value={state.name}
          fullWidth
        >
          {[...Array(30)].map((i, j) => (
            <MenuItem key={j} value={j} >
              option-{j}
            </MenuItem>
          ))}
        </VdsSelect>
    );
}
`);
export const SingleSelection_Example = () => {

  const [state, setState] = React.useState<{ [P in string]: unknown }>({});

  const handleChange = (key: string, value: unknown) => { setState({ ...state, [key]: value }); }

  return (
    <Grid container spacing={2}>
      <Grid item lg={3}>
        <VdsSelect
          disabled={false}
          label='Select text label*'
          MenuProps={{
            PaperProps: {
              style: {
                maxHeight: 224,
                width: 250,
              },
            }
          }}
          onChange={(ev) => handleChange('name', ev.target.value)}
          value={state.name}
          fullWidth
        >
          {[...Array(30)].map((_i, j) => (
            <MenuItem key={j} value={j} >
              {`option-${j}`}
            </MenuItem>
          ))}
        </VdsSelect>
        <div>
          <h4>Default</h4>
        </div>
      </Grid>
      <Grid item lg={3}>
        <VdsSelect
          disabled
          label='Select text label*'
          MenuProps={{
            PaperProps: {
              style: {
                maxHeight: 224,
                width: 250,
              },
            }
          }}
          onChange={(ev) => handleChange('name2', ev.target.value)}
          value={state.name1}
          fullWidth
        >
          {[...Array(30)].map((_i, j) => (
            <MenuItem key={j} value={j} >
              {`option-${j}`}
            </MenuItem>
          ))}
        </VdsSelect>
        <div>
          <h4>Disabled</h4>
        </div>
      </Grid>
      <Grid item lg={3}>
        <VdsSelect
          readOnly
          label='Select text label*'
          MenuProps={{
            PaperProps: {
              style: {
                maxHeight: 224,
                width: 250,
              },
            }
          }}
          onChange={(ev) => handleChange('name3', ev.target.value)}
          value={state.name1}
          fullWidth
        >
          {[...Array(30)].map((_i, j) => (
            <MenuItem key={j} value={j} >
              {`option-${j}`}
            </MenuItem>
          ))}
        </VdsSelect>
        <div>
          <h4>ReadOnly</h4>
        </div>
      </Grid>
      <Grid item lg={3}>
        <VdsSelect
          label='Select text label*'
          error={true}
          errorText='Error message here'
          MenuProps={{
            PaperProps: {
              style: {
                maxHeight: 224,
                width: 250,
              },
            }
          }}
          onChange={(ev) => handleChange('name4', ev.target.value)}
          value={state.name1}
          fullWidth
        >
          {[...Array(30)].map((_i, j) => (
            <MenuItem key={j} value={j} >
              {`option-${j}`}
            </MenuItem>
          ))}
        </VdsSelect>
        <div>
          <h4>Error</h4>
        </div>
      </Grid>
    </Grid>
  );
}

//#endregion
